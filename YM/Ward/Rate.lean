import Mathlib.Analysis.Calculus.Taylor
import YM.Analysis.Homogeneous




/-!
# Factorial proof to release all extreme position analyticity

Real parameter ONLY. Value jets of scalar comparator at one point ⇒ center estimate there.
To use analyticity extension need estimates nearby (or uniform from group).
Do **not** infer analytic S from equality of comparing jets at line alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Analysis
open Metric Function Set Filter
open scoped Topology NNReal ENNReal InnerProductSpace ContDiff BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E)

def Power (C ρ : ℝ) (n : ℕ) := C * (ρ ^ n)⁻¹ * (Nat.factorial n:ℝ)

theorem center (x : ℝ) (hf : AnalyticAt ℝ f x) : ∃ C > (0:ℝ), ∃ ρ > (0:ℝ), ∀ n,
    ‖iteratedDeriv n f x‖ ≤ Power C ρ n := by
  obtain ⟨p,r,hr⟩ := hf
  obtain ⟨A,hA,hp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr.r_pos
  obtain ⟨C,hC,H⟩ := p.norm_mul_pow_le_of_lt_radius (hp.trans_le hr.r_le)
  replace hA : 0<(A:ℝ) := ENNReal.coe_pos.mp hA
  refine ⟨C,hC,A,hA,fun n => ?_⟩
  rw [iteratedDeriv_eq_iteratedFDeriv,← hr.factorial_smul,← Nat.cast_smul_eq_nsmul ℝ,norm_smul,Real.norm_natCast]
  rw [Power,mul_comm (Nat.factorial n:ℝ)]
  gcongr
  apply le_trans ((p n).le_opNorm (fun _ => (1:ℝ)))
  simpa only [norm_one, Finset.prod_const_one,mul_one,← div_eq_mul_inv] using
    ((le_div_iff₀ (pow_pos hA n)).2 (H n)) -- direction check

omit [CompleteSpace E] in
private lemma maxpow (x : ℝ) (n : ℕ) (q : ℝ≥0) (hq : 0<(q:ℝ)) (C : ℝ)
    (hg : ‖iteratedDeriv n f x‖ ≤ Power C q n) : ‖Tensor.coeff f n x‖*(q:ℝ)^n ≤ C := by
  rw [Tensor.coeff,norm_smul,norm_inv,Real.norm_natCast,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  calc _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) (by positivity)
       _ = C := by unfold Power; field_simp

private theorem groups (h : ContDiff ℝ ∞ f) (C ρ : ℝ) (hC : 0<C) (hr : 0<ρ)
    (hh : ∀ n x, ‖iteratedDeriv n f x‖ ≤ Power C ρ n) (a x : ℝ) (ht : x∈ Ioo a (a+ρ/2)) :
    let u : FormalMultilinearSeries ℝ ℝ E := fun n => Tensor.coeff f n a
    x-a ∈ eball 0 u.radius ∧ u.sum (x-a)=f x := by
  lift ρ to ℝ≥0 using hr.le
  intro u
  have hv : (ρ:ℝ≥0∞) ≤ u.radius := u.le_radius_of_bound C fun n => maxpow f a n ρ hr C (hh n a)
  let d := x-a
  obtain ⟨ha,hx⟩ := ht
  have hd : 0<d := sub_pos.mpr ha
  have hr' : x-a∈ eball 0 (ρ:ℝ≥0∞) := by
    rw [Metric.eball_coe, mem_ball, Real.dist_eq, sub_zero, abs_of_pos hd]; linarith
  have hq : d∈ eball 0 u.radius := eball_subset_eball hv hr'
  refine ⟨hq,?_⟩
  have H_ (n : ℕ) : ContDiff ℝ n f := h.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu (n : ℕ) : ContDiffOn ℝ (↑n+1) f (Icc a x) := by
    rw [← Nat.cast_one (R := WithTop ℕ∞), ← Nat.cast_add]; exact (H_ _).contDiffOn
  have hf n y (hy : y∈ Icc a x) : iteratedDerivWithin n f (Icc a x) y=iteratedDeriv n f y :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ha) ((H_ _).contDiffAt) hy
  let P n := ∑ i ∈ Finset.range (n+1), u i (fun _ => d)
  have hw n : taylorWithinEval f n (Icc a x) a x = P n := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro i _
    have he : u.coeff i=(↑(Nat.factorial i):ℝ)⁻¹ • iteratedDeriv i f a := by
      rw [iteratedDeriv_eq_iteratedFDeriv]; rfl
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff (p := u),he,
      hf i a (left_mem_Icc.mpr ha.le)]
    simp only [Finset.prod_const,Finset.card_univ, Fintype.card_fin, smul_smul, mul_comm (d^i)]; rfl
  have hm := (u.hasSum hq).tendsto_sum_nat
  let θ := 2*(d/(ρ:ℝ))
  have hθ : 0 < θ := by unfold θ; positivity
  have hrθ : θ < 1 := by unfold θ; rw [← mul_div_assoc, div_lt_one hr]; dsimp [d] at *; linarith
  have hh_ (n : ℕ) : dist (P n) (f x) ≤ C * θ^(n+1) := by
    rw [dist_comm,dist_eq_norm,← hw]
    apply le_trans (taylor_mean_remainder_bound ha.le (C := Power C ρ (n+1)) (hu n)
      (right_mem_Icc.mpr ha.le) (fun y hy => by rw [hf _ _ hy]; exact hh _ _))
    calc
      _ = C * (d/(ρ:ℝ))^(n+1) * ((n+1:ℕ):ℝ) := by unfold Power; rw [Nat.factorial_succ,Nat.cast_mul]; unfold d; field_simp; rw [← mul_pow, mul_div_cancel₀ _ hr.ne']
      _ ≤ C * (d/(ρ:ℝ))^(n+1) * 2^(n+1) := by
        have he : (n+1) ≤ 2^(n+1) := Nat.le_of_lt (Nat.lt_pow_self (by norm_num))
        apply mul_le_mul_of_nonneg_left _ (by positivity); exact_mod_cast he
      _ = C * θ^(n+1) := by unfold θ; rw [mul_pow]; ring
  have hn : Tendsto (fun n : ℕ => C * θ^(n+1)) atTop (𝓝 0) := by
    have he := tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hrθ
    simpa only [mul_zero,Function.comp_apply] using (he.comp (tendsto_add_atTop_nat 1)).const_mul C
  apply tendsto_nhds_unique (f := P) (hm.comp (tendsto_add_atTop_nat 1))
  exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) hh_ hn)

theorem builds (h : ContDiff ℝ ∞ f) (C ρ : ℝ) (hC : 0<C) (hr : 0<ρ)
    (hh : ∀ n x, ‖iteratedDeriv n f x‖ ≤ Power C ρ n) (x : ℝ) : AnalyticAt ℝ f x := by
  let a := x-ρ/4
  have hx : x∈ Ioo a (a+ρ/2) := by constructor <;> dsimp only [a] <;> linarith
  let u : FormalMultilinearSeries ℝ ℝ E := fun n => Tensor.coeff f n a
  have he := groups f h C ρ hC hr hh a x hx
  have hu : AnalyticAt ℝ (fun y => u.sum (y-a)) x :=
    ((FormalMultilinearSeries.analyticOnNhd (p := u) _ he.1).comp (f := fun y => y-a)
      (analyticAt_id.sub analyticAt_const))
  exact hu.congr ( (show ∀ᶠ y in 𝓝 x, y∈ Ioo a (a+ρ/2) from Ioo_mem_nhds hx.1 hx.2) |>.mono (fun i hi => (groups f h C ρ hC hr hh a i hi).2))
end YM.Analysis
