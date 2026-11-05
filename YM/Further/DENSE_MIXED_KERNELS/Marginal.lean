import YM.Bid.Loan
import YM.Further.DENSE_MIXED_KERNELS.ExponentialJets
import YM.Further.DENSE_MIXED_KERNELS.Gaussian


/-!
# Coarse V derivative prices for one conditional Gaussian

Take the covariance of the **marginal on the actual union** first. Q(x,x) includes
1/2, uses inverse marginal covariance. No claim that estimates on inverse of larger
precision automatically apply. Log-determinant derivative costs here are paid on
the actual normalization integral. Real, jointly with moving Z arguments (e.g.
others in the product read a `U_e`, so `Z_e` no longer held fixed). Will use
with frozen parameters for the whole word.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels.Gaussian
open Function Filter Module MeasureTheory Measure Lattice RG Wilson
open scoped NNReal ENNReal Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

-- coercivity is open (also when parameters not serialized via symmetric matrices)
def Firm (Q : Quad E) : Prop := ∃ c : ℝ,0<c ∧ ∀ x,c*‖x‖^2 ≤ Q x x

private def entry (x : E) : Quad E →L[ℝ] ℝ := -(ContinuousLinearMap.apply ℝ ℝ x ∘L
    ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) x)
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma entry_apply (x : E) (Q : Quad E) : entry x Q = -(Q x x) := rfl
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma entry_le (x : E) (Q : Quad E) : ‖entry x Q‖ ≤ ‖x‖^2 * ‖Q‖ := by
  rw [entry_apply,norm_neg]
  have h : ‖Q x x‖ ≤ ‖Q‖ * ‖x‖ * ‖x‖ := Q.le_opNorm₂ x x
  linarith only [h]

private lemma exp_norm (r : ℝ) (k : ℕ) : ‖iteratedFDeriv ℝ k Real.exp r‖ = Real.exp r := by
  have hv : iteratedDeriv k Real.exp = Real.exp := by
    induction k with
    | zero => exact iteratedDeriv_zero
    | succ k ih => rw [iteratedDeriv_succ',Real.deriv_exp]; exact ih
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,hv,Real.norm_of_nonneg (Real.exp_pos r).le]

private lemma liftCL {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] (L : D →L[ℝ] ℝ) (k : ℕ) :
    ContDiff ℝ k L := L.contDiff

-- state this bound using only the one-functional cost
private lemma curve {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] (L : D→L[ℝ]ℝ) (x : D)
    (i : ℕ) {C : ℝ} (hC : 0≤C) (he : ∀ z,‖L z‖ ≤ C * ‖z‖) :
    ‖iteratedFDeriv ℝ i (Real.exp ∘ L) x‖ ≤ Real.exp (L x)*C^i := by
  rw [L.iteratedFDeriv_comp_right (n:=i) Real.contDiff_exp x (le_refl (i:WithTop ℕ∞))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  simp only [exp_norm,Finset.prod_const,Finset.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg L) (L.opNorm_le_bound hC he) _) (Real.exp_pos _).le

variable {Q J : Quad E}
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma stays {c : ℝ} (h : ∀ x,c*‖x‖^2 ≤ Q x x) (hv : ‖J-Q‖ ≤ c/2) :
    ∀ x : E,(Q x x)/2 ≤ J x x := by
  intro x
  have hy := calc
    ‖entry x (J-Q)‖ ≤ ‖x‖^2 * ‖J-Q‖ := entry_le ..
    _ ≤ ‖x‖^2 * (c/2) := mul_le_mul_of_nonneg_left hv (by positivity)
  rw [show entry x (J-Q) = entry x J-entry x Q from map_sub (entry x) J Q,entry_apply,entry_apply, Real.norm_eq_abs] at hy; linarith [(abs_le.mp hy).2,h x]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma Firm.openly (h : Firm Q) : ∀ᶠ T in 𝓝 Q,Firm T := by
  obtain ⟨c,hc,hh⟩ := h
  filter_upwards [Metric.closedBall_mem_nhds Q (by positivity : 0<c/2)] with v hv
  exact ⟨c/2,by positivity,fun x => le_trans (by linarith [hh x] : c/2*‖x‖^2 ≤ Q x x/2)
    (stays hh (by rw [Metric.mem_closedBall,show dist v Q = ‖v-Q‖ from dist_eq_norm v Q] at hv; exact hv) x)⟩



/-- No budget asserted by this local domination. -/
theorem Firm.dominated (k : ℕ) (H : Firm Q) : Window μ k Q (fun x T => raw T x) := by
  obtain ⟨c,hc,h⟩ := H
  let s := Metric.ball Q (c/2)
  let B : Quad E := (1/2:ℝ) • Q
  have ht x : B x x=Q x x/2 := by unfold B; simp only [_root_.smul_apply,smul_eq_mul]; ring
  have hj x : c/2*‖x‖^2 ≤ B x x := by rw [ht]; linarith [h x]
  refine ⟨s,Metric.mem_ball_self (by positivity),Metric.isOpen_ball,
    fun x => (by
      have hg : ContDiff ℝ k (fun t : Quad E=>entry x t) := liftCL (D:=Quad E) (entry x) k
      exact (Real.contDiff_exp.comp hg).contDiffOn),
    fun A _ => (raw_cont A).aestronglyMeasurable,fun x => raw B x*(1+‖x‖)^(2*k),
    polynomial_integrable μ (by positivity) hj _,fun x A hA i hi => ?_⟩
  have hX : raw A x ≤ raw B x := by
    apply Real.exp_monotone; rw [ht]; exact neg_le_neg (stays h (by
      have hs : dist A Q ≤ c/2 := Metric.mem_closedBall.mp (Metric.ball_subset_closedBall hA)
      rw [show dist A Q = ‖A-Q‖ from dist_eq_norm A Q] at hs; exact hs) x)
  have ev := curve (D:=Quad E) (entry x) A i (C:=‖x‖^2) (by positivity) (entry_le x)
  apply le_trans ev
  change raw A x * _ ≤ _
  refine mul_le_mul hX ?_ (by positivity) (Real.exp_pos _).le
  rw [pow_mul]
  calc
    _ ≤ ((1+‖x‖)^2)^i := pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg x]) _
    _ ≤ _ := pow_le_pow_right₀ (one_le_pow₀ (by linarith [norm_nonneg x])) hi



variable {k : ℕ} {c C t s : ℝ} {G : Gauge} {n : Side} {U : Config G n} {P : Directions G n → Prop}
variable {W : Config G n → Quad E} (hc : 0<c) (hW : ∀ x, c*‖x‖^2 ≤ W U x x)
    (hp : Pitch W U P k C t) (ht : 0≤t) (hC : 1≤C)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma eval_pitch (hp : Pitch W U P k C t) (x : E) : Pitch (fun v => -W v x x) U P k
    ((1+‖x‖)^2*C) t := by
  refine Pitch.linear hp (entry x) (C:= (1+‖x‖)^2) (fun T => ?_) (by positivity)
  apply (entry_le x T).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg T)); nlinarith [norm_nonneg x]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma steady (hp : Pitch W U P k C t) (x : E) (ht : 0≤t) (hC : 1≤C) : Pitch (fun v => raw (W v) x) U P k
    (raw (W U) x) (2^k*C*t*(1+‖x‖)^2) := by
  have hv : 1 ≤ (1+‖x‖)^2*C := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg x])) hC
  rw [show (2:ℝ)^k*C*t*(1+‖x‖)^2=2^k*((1+‖x‖)^2*C*t) by ring]; unfold raw
  exact ((eval_pitch hp x).pulse ht hv).flare (by positivity)

def stall (d k : ℕ) (c C t : ℝ) := 2^k*C*t*expense d (2*k) c
lemma expense_ge {c : ℝ} (hc : 0<c) (n k : ℕ) : 1≤expense n k c := by
  apply one_le_mul_of_one_le_of_one_le (one_le_pow₀ ?_) (Real.one_le_exp zero_le_one)
  refine le_trans (by norm_num : (1:ℝ) ≤ 2) (le_add_of_nonneg_right (by positivity))

include hc hW hp ht hC in
lemma drive :
    Pitch (zMass μ ∘ W) U P k (zMass μ (W U)) (stall (finrank ℝ E) k c C t) := by
  let f (x : E) v := raw (W v) x
  have h : Firm (W U) := ⟨_,hc,hW⟩
  have H : Varies μ k U f := by
    unfold Varies; refine (Window.comp (μ:=μ) (f:=fun x T=>raw T x) (T:=W ∘ increment U) (d:=0) ?_ hp.smooth)
    rw [comp_apply,increment_zero]
    exact h.dominated μ k
  refine ⟨H.integrate,fun l hl hD => ?_⟩
  change ‖leftDerivs (fun v => ∫ i,f i v ∂μ) l U‖ ≤ _
  rcases eq_or_ne l [] with hv|hv
  · subst l; change ‖zMass μ (W U)‖ ≤ zMass μ (W U) * _ ^ ([]:List (Directions G n)).length
    rw [Real.norm_of_nonneg (zMass_pos μ hc hW).le,List.length_nil,pow_zero,mul_one]
  have hl' : 0 < l.length := List.length_pos_iff.mpr hv
  let e := l.length; let r := (2:ℝ)^k*C*t
  let b x := raw (W U) x * (1+‖x‖)^(2*k)
  have hr : 0≤r := by unfold r; positivity
  have hV : ∀ x, ‖leftDerivs (f x) l U‖ ≤ r^e * b x := by
    intro x
    apply ((steady hp x ht hC).bounds l hl hD).trans; unfold b
    change _*(r*(1+‖x‖)^2)^l.length ≤ _
    rw [mul_left_comm (r^e),mul_pow]; refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr e)
    rw [← pow_mul]; exact pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
  rw [H.turns l hl]; apply (norm_integral_le_integral_norm _).trans
  apply le_trans (integral_mono ((H.post l (show 0+l.length ≤ k by omega)).reads.norm)
    ((show Integrable b μ from polynomial_integrable μ hc hW _).const_mul (r^e)) hV)
  rw [integral_const_mul]
  apply le_trans (mul_le_mul_of_nonneg_left (raw_bill μ hc hW _) (by positivity : 0≤r^e))
  unfold stall
  let L := expense (finrank ℝ E) (2*k) c
  change r^e*(L*zMass μ (W U))≤zMass μ (W U)*(r*L)^e
  rw [←mul_assoc,mul_pow r L e,mul_comm (zMass μ (W U))]
  apply mul_le_mul_of_nonneg_right _ (zMass_pos μ hc hW).le
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr e)
  nth_rw 1 [← pow_one L]; exact pow_le_pow_right₀ (expense_ge hc ..) hl'

include hc hW hp ht hC in
/-- Relative derivatives when Z itself moves (held-U representation).
Noncircular quantitative producer. No output covariance bounds hidden
inside a bound on inverse-mass derivatives. -/
theorem dynamic {z : Config G n → E} (hz : Pitch z U P k (1+‖z U‖) s) (hs : 0≤s) :
    Pitch (fun v => pdf μ (W v) (z v)) U P k (pdf μ (W U) (z U))
      ( (2:ℝ)^k*C*(1+‖z U‖)^2*(t+2*s) + 3^k*stall (finrank ℝ E) k c C t ) := by
  let K (v : Config G n) := W v (z v) (z v)
  let r := 1 + ‖z U‖
  have hr : 1 ≤ r := le_add_of_nonneg_right (norm_nonneg _)
  have hv := Pitch.clm (Pitch.clm hp hz) hz
  have he : Pitch (fun v => -K v) U P k (C*r^2) (t+2*s) := by
    rw [show C*r^2=C*(1+‖z U‖)*(1+‖z U‖) by unfold r; ring, show t+2*s=t+s+s by ring]; exact Pitch.negate hv
  let M := (2:ℝ)^k*C*(1+‖z U‖)^2*(t+2*s)
  have hc₁ : 1 ≤ C*r^2 := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hr)
  have hK : Pitch (fun v => raw (W v) (z v)) U P k (raw (W U) (z U)) M := by
    unfold M; rw [show (2:ℝ)^k*C*(1+‖z U‖)^2*(t+2*s)=(2:ℝ)^k*(C*r^2*(t+2*s)) by unfold r; ring]
    exact Pulse.flare (he.pulse (by positivity) hc₁) (by positivity : 0 ≤ C*r^2*(t+2*s))
  let x : Config G n → ℝ := zMass μ ∘ W
  have hs' : 0≤stall (finrank ℝ E) k c C t := mul_nonneg (by positivity) (zero_le_one.trans (expense_ge hc ..))
  have hh := Pitch.reverse (f:=x) (drive μ hc hW hp ht hC) hs' (zMass_pos μ hc hW)
  unfold pdf; simp_rw [div_eq_mul_inv]; exact Pitch.real_mul hK hh

end YM.Further.DenseMixedKernels.Gaussian
