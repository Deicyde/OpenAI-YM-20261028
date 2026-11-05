import YM.Extra.WILSON_STARTUP.Author
import YM.Extra.WILSON_STARTUP.MixPay

/-! # Startup grants for all marker arities under width control -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Mixture
open Function Filter RG Lattice Wilson Finset Overlay Source Mix Labels
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n d : ℕ} {m : Side} {V : Type} {F : Frame G d} {S : SectionData F}

def order (F : Frame G d) := max 1 (Mark.slotOrder F)

def Cap (v : F.Coeff) (S : SectionData F) (C g w : ℝ) :=
    (w*F.coeffSize v) * (Mark.price S*C) ≤ g ^ order F

lemma core_le (v : F.Coeff) : F.coeffSize (F.core v) ≤ F.coeffSize v := by
  unfold Frame.core Frame.coeffSize; refine sum_le_sum fun i _ => ?_; by_cases hi : i=0 <;> simp [hi]

lemma diameter_cost {b : BudgetPoint} (hr : Mark.diameter S ≤ b.B) (o : Site m) : coverNumber b.B (S.footprint o) ≤ 5^4 := by
  refine (Lattice.Corona.cover_mono (X:=pad b o) ?_ _).trans (Start.pad_cost o)
  intro x hx
  rw [mem_pad, separation_comm]
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
  rw [separation,add_sub_cancel_right]
  apply le_trans (b:=Mark.diameter S) _ (by omega)
  exact Finset.sup_le fun i hi => (Lattice.Corona.lap ..).trans ((le_sup (f:=fun j : Axis => (y j).natAbs) hi).trans (le_sup
    (f:=fun y : Cover => Finset.univ.sup fun j => (y j).natAbs) hy))

def excess (b : BudgetPoint) := Start.overhead b * ((b.order+1:ℕ):ℝ)

lemma fitted {b : BudgetPoint} (o : V → Site m) (v : V → F.Coeff) {w C g : ℝ} (hC : 1 ≤ C)
    (hg : 0 < g) (h : g ≤ b.threshold) (he : g * excess b ≤ 1) (hw : 0 < w) (hc : ∀ i, Cap (v i) S C g w)
    (hD : Mark.diameter S ≤ b.B) (ht : Bid.Credit S b.order b.power C) : DataCost S o b v C w := by
  let k := Mark.slotOrder F
  let l := order F
  have hg' := h.trans b.threshold_le
  let c := fun i => w * F.coeffSize (v i) * (Mark.price S * C)
  have hc' (i) : w * F.coeffSize (v i) * (Mark.price S * C) ≤ g^l := hc i
  have hx := Mark.price_ge_one S
  have h1 := pow_le_pow_of_le_one hg.le hg' (show 1 ≤ l from le_max_left ..)
  rw [pow_one] at h1
  have hb := pow_le_pow_of_le_one hg.le hg' (show k ≤ l from le_max_right ..)
  have hi (i) := core_le (v i)
  have hn (i) := Mark.coeff_nn (F.core (v i))
  have hz (i) : w*F.coeffSize (F.core (v i))*C ≤ g^l := by
    refine le_trans ?_ (hc' i)
    have := Mark.coeff_nn (v i)
    gcongr
    · exact hi i
    exact le_mul_of_one_le_left (zero_le_one.trans hC) hx
  refine ⟨zero_le_one.trans hC,ht,hw, fun i => le_trans ?_ ((hc' i).trans (h1.trans hg')), fun i => ?_, fun i => ?_⟩
  · refine le_trans (b:=w*F.coeffSize (v i)) ?_ (le_mul_of_one_le_right (mul_nonneg hw.le (Mark.coeff_nn ..)) (one_le_mul_of_one_le_of_one_le hx hC))
    gcongr; exact single_le_sum (fun j _ => norm_nonneg (v i j)) (mem_univ 0)
  · calc
      _ = Real.exp (b.supportExponent * coverNumber b.B (S.footprint (o i))) * ((b.order+1:ℕ):ℝ) * (w*F.coeffSize (F.core (v i))*C) := by unfold ink BudgetPoint.mass; ring
      _ ≤ excess b * g := by
        unfold excess Start.overhead
        have hI := hn i
        have := b.exponent_pos; gcongr
        · exact_mod_cast diameter_cost hD (o i)
        · exact (hz i).trans h1
      _ ≤ 1 := by rwa [mul_comm]
  · have hr : 0 ≤ b.threshold⁻¹^k := by have := b.threshold_pos; positivity
    calc
      _ = b.threshold⁻¹^k * ((w*F.coeffSize (F.core (v i))) * Mark.price S) := by unfold fullCost Mark.scale; ring
      _ ≤ b.threshold⁻¹^k * c i := by
        have := Mark.coeff_nn (v i)
        unfold c; gcongr
        · exact hi i
        exact le_mul_of_one_le_right (zero_le_one.trans hx) hC
      _ ≤ b.threshold⁻¹^k * b.threshold^k := mul_le_mul_of_nonneg_left ((hc i).trans (hb.trans (pow_le_pow_left₀ hg.le h k))) hr
      _ = _ := by simp [b.threshold_pos.ne']

structure Extras (a : Levels G) (N : ℕ) : Prop where
  size : 8 ≤ a.clock.coverSize N
  overhead : a.clock.hatCoupling N * excess (a.budget N) ≤ 1
  packets : ∃ σ κ γ, Start.Loan (Start.expand (a.budget N)) (a.clock.hatBeta N / 2) σ κ γ ∧ Bid.quote κ (Real.exp γ-1) ≤ 1/2

lemma afford (G : Gauge) (A : Stage) : ∀ᶠ x : ℝ in atTop, ∀ a : Levels G, ∀ N,
    a.params N=A → a.clock.hatBeta N=x → Extras a N := by
  have H := (Timing.shrinking.mul_const (Real.exp (A.supportExponent *5^4)*((A.order+1:ℕ):ℝ))).eventually (ge_mem_nhds (by simp : 0*_<(1:ℝ)))
  have ht : ∀ᶠ s in atTop, Timing.normK s ≤ 1/2 := by
    refine Eventually.of_forall fun s => ?_
    have hx : 1 ≤ Real.exp ((Real.log s)^2/5) := Real.one_le_exp (by positivity)
    rw [Timing.normK,Real.exp_neg, one_div]; refine (inv_le_inv₀ (by positivity) (by norm_num)).mpr ((by linarith only [Real.add_one_le_exp 1] : (2:ℝ) ≤ Real.exp 1).trans
      (Real.exp_le_exp.mpr hx))
  filter_upwards [Real.tendsto_log_atTop.eventually (Timing.nballs.eventually_ge_atTop 8), Real.tendsto_log_atTop.eventually H,
    Real.tendsto_log_atTop.eventually ht, Real.tendsto_log_atTop.eventually (Timing.loan (A.supportExponent+8)), eventually_gt_atTop (0:ℝ)] with x h1 h2 h3 h4 hx a N ha hN
  let s := Real.log x; let b := Start.expand (a.budget N)
  have hb : a.clock.coverSize N = Timing.balls s := congr_arg (fun x => Timing.balls (Real.log x)) hN
  have hp : a.clock.hatCoupling N = Real.exp (-(s/2)) := by
    unfold Calendar.hatCoupling; rw [hN,Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; unfold s; ring_nf
  obtain ⟨hh,hμ⟩ := h4 b (by
    dsimp only [b,Start.expand,Levels.budget,Calendar.threshold,Calendar.monitor,Timing.temp]
    rw [hp,Real.exp_add]; unfold s; rw [hN]) hb (congr_arg (fun p : Stage => p.supportExponent + 8) ha)
  rw [Real.exp_log hx] at hh
  nth_rw 1 [← hN] at hh
  refine ⟨hb ▸ h1, le_trans ?_ h2,_,_,_,hh,hμ.trans h3⟩
  rw [hp]; change Real.exp (-(s/2)) * (Real.exp ((a.params N).supportExponent*5^4) * _) ≤ _
  dsimp only [Levels.budget]; rw [ha]; unfold Timing.temp; gcongr
  unfold s; linarith [sq_nonneg (Real.log (Real.log x))]
end YM.WilsonStartup.Mixture
