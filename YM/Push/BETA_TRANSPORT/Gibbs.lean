import YM.Push.BETA_TRANSPORT.Weight

/-!
# Real shifts of bounded energies

The two separate uses of probability normalization (Wilson partition and
block noise) will give **two** subtraction terms on differentiation. A
sector's `crownGap` in contrast gives an unnormalized shift.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Push.BetaTransport
open MeasureTheory Filter Set
open scoped Topology
variable {α : Type*} [MeasurableSpace α]



namespace Gibbs

def factor (H : α → ℝ) (β : ℝ) (x : α) : ℝ := Real.exp (-β*H x)
def Z (μ : Measure α) (H : α → ℝ) (β : ℝ) := ∫ x, factor H β x ∂μ
def tilt (μ : Measure α) (H : α → ℝ) (β : ℝ) (x : α) := (Z μ H β)⁻¹ * factor H β x
def mean (μ : Measure α) (H : α → ℝ) (β : ℝ) := ∫ x, tilt μ H β x * H x ∂μ
def tiltSlope (μ : Measure α) (H : α → ℝ) (β : ℝ) (x : α) := tilt μ H β x * (mean μ H β - H x)

/-- Crude denominator and density prices (lattice dependence via A); no large-volume lower
bound assumed for either partition function. -/
def cost (A R : ℝ) := Real.exp (R*A)

lemma cost_pos (A R : ℝ) : 0 < cost A R := Real.exp_pos _


omit [MeasurableSpace α] in
lemma factor_pos (H : α → ℝ) (b : ℝ) (x : α) : 0 < factor H b x := Real.exp_pos _
lemma factor_meas {H : α → ℝ} (h : Measurable H) (b : ℝ) : Measurable (factor H b) :=
  (measurable_const.mul h).exp
omit [MeasurableSpace α] in
lemma factor_hasDerivAt (H : α → ℝ) (b : ℝ) (x : α) :
    HasDerivAt (factor H · x) (factor H b x * (- H x)) b := by
  simpa [factor] using! (((hasDerivAt_id b).neg.mul_const (H x)).exp)
omit [MeasurableSpace α] in
lemma factor_bounds {H : α → ℝ} {A b R : ℝ} (ha : ∀ x, ‖H x‖ ≤ A) (hb : |b| ≤ R) (x : α) :
    (cost A R)⁻¹ ≤ factor H b x ∧ factor H b x ≤ cost A R := by
  have he : |-b*H x| ≤ R*A := by
    rw [abs_mul,abs_neg]; exact mul_le_mul hb (ha x) (abs_nonneg _) ((abs_nonneg _).trans hb)
  rw [cost, ← Real.exp_neg,factor]
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp he).1, Real.exp_le_exp.mpr (abs_le.mp he).2⟩
lemma factor_weight {H : α → ℝ} (h : Measurable H) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ x, ‖H x‖ ≤ A) :
    WeightEstimate (factor H) (fun b x => factor H b x * (- H x)) A (cost A) := by
  refine ⟨factor_meas h,fun b => (factor_meas h b).mul h.neg,fun _ _ => (factor_pos ..).le,
    fun hb x => (factor_bounds ha hb x).2, fun b x => ?_,factor_hasDerivAt H,hA,fun R _ => (cost_pos ..).le⟩
  rw [norm_mul,norm_neg,Real.norm_of_nonneg (factor_pos ..).le, mul_comm A]
  exact mul_le_mul_of_nonneg_left (ha x) (factor_pos ..).le

structure EnergyEstimate (H : α → ℝ) (A : ℝ) : Prop where
  measurable : Measurable H
  nonneg : ∀ x, 0 ≤ H x
  bound : ∀ x, H x ≤ A
  cap : 0 ≤ A

namespace EnergyEstimate
variable {H : α → ℝ} {A : ℝ} (h : EnergyEstimate H A)
include h
lemma norm_le (x : α) : ‖H x‖ ≤ A := (Real.norm_of_nonneg (h.nonneg x)).trans_le (h.bound x)
lemma factor_estimate : WeightEstimate (factor H) (fun b x => factor H b x * (- H x)) A (cost A) :=
  factor_weight h.measurable h.cap h.norm_le
variable {μ : Measure α} [IsProbabilityMeasure μ]
lemma factor_integrable (b : ℝ) : Integrable (factor H b) μ :=
  Integrable.of_bound (factor_meas h.measurable b).aestronglyMeasurable _ (Eventually.of_forall fun x =>
    (Real.norm_of_nonneg (factor_pos ..).le).trans_le (h.factor_estimate.le le_rfl x))
lemma Z_bounds {b R : ℝ} (hb : |b| ≤ R) : (cost A R)⁻¹ ≤ Z μ H b ∧ Z μ H b ≤ cost A R := by
  have he := factor_bounds h.norm_le hb
  have ht := integral_mono (integrable_const _) (h.factor_integrable (μ:=μ) b) fun x => (he x).1
  have hu := integral_mono (h.factor_integrable (μ:=μ) b) (integrable_const _) fun x => (he x).2
  exact ⟨by simpa [Z] using ht, by simpa [Z] using hu⟩
lemma Z_pos (b : ℝ) : 0 < Z μ H b := (inv_pos.mpr (cost_pos ..)).trans_le (h.Z_bounds (le_refl |b|)).1
lemma tilt_pos (b : ℝ) (x : α) : 0 < tilt μ H b x := mul_pos (inv_pos.mpr (h.Z_pos _)) (factor_pos ..)
omit [IsProbabilityMeasure μ] in
lemma tilt_meas (b : ℝ) : Measurable (tilt μ H b) := measurable_const.mul (h.factor_estimate.measurable b)
lemma tilt_bounds {b R : ℝ} (hb : |b| ≤ R) (x : α) :
    (cost A R * cost A R)⁻¹ ≤ tilt μ H b x ∧ tilt μ H b x ≤ cost A R * cost A R := by
  rw [mul_inv_rev]
  exact ⟨mul_le_mul ((inv_le_inv₀ (cost_pos ..) (h.Z_pos b)).mpr (h.Z_bounds hb).2)
    (factor_bounds h.norm_le hb x).1 (inv_pos.mpr (cost_pos ..)).le (inv_pos.mpr (h.Z_pos b)).le,
    mul_le_mul (by simpa using (inv_le_inv₀ (h.Z_pos b) (inv_pos.mpr (cost_pos ..))).mpr (h.Z_bounds hb).1)
      (factor_bounds h.norm_le hb x).2 (factor_pos ..).le (cost_pos ..).le⟩
lemma tilt_integrable (b : ℝ) : Integrable (tilt μ H b) μ :=
  (h.factor_integrable b).const_mul _
lemma total (b : ℝ) : (∫ x, tilt μ H b x ∂μ) = 1 := by
  simp only [tilt,integral_const_mul]; exact inv_mul_cancel₀ (h.Z_pos (μ:=μ) b).ne'
lemma mean_bound (b : ℝ) : 0 ≤ mean μ H b ∧ mean μ H b ≤ A := by
  refine ⟨integral_nonneg fun x => mul_nonneg (h.tilt_pos b x).le (h.nonneg x), ?_⟩
  calc mean μ H b ≤ ∫ x, tilt μ H b x * A ∂μ :=
          integral_mono ((h.tilt_integrable b).mul_bdd h.measurable.aestronglyMeasurable (Eventually.of_forall h.norm_le))
            ((h.tilt_integrable b).mul_const _) fun x => mul_le_mul_of_nonneg_left (h.bound x) (h.tilt_pos b x).le
       _ = A := by rw [integral_mul_const,h.total,one_mul]
lemma Z_hasDerivAt (b : ℝ) : HasDerivAt (Z μ H) (- (mean μ H b) * Z μ H b) b := by
  have he := h.factor_estimate.integral_derivative (μ:=μ) (integrable_const (1:ℝ)) b
  simp only [smul_eq_mul,mul_one] at he
  unfold mean tilt
  simp_rw [mul_assoc,integral_const_mul]
  simp_rw [mul_neg,integral_neg] at he
  convert he using 1 <;> try rfl
  field_simp [(h.Z_pos (μ:=μ) b).ne']
lemma tilt_hasDerivAt (b : ℝ) (x : α) : HasDerivAt (tilt μ H · x) (tiltSlope μ H b x) b := by
  have hz := h.Z_pos (μ:=μ) b
  have he : (tiltSlope μ H b x) = - (-(mean μ H b) * Z μ H b) / Z μ H b ^ 2 * factor H b x +
      (Z μ H b)⁻¹ * (factor H b x * (-H x)) := by unfold tiltSlope tilt; field_simp; ring
  rw [he]
  exact ((h.Z_hasDerivAt b).inv hz.ne').mul (factor_hasDerivAt H b x)



variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

end EnergyEstimate

omit [MeasurableSpace α] in
@[simp] lemma factor_zero (H : α → ℝ) (x : α) : factor H 0 x = 1 := by simp [factor]
@[simp] lemma Z_zero (μ : Measure α) [IsProbabilityMeasure μ] (H : α → ℝ) : Z μ H 0 = 1 := by simp [Z]
@[simp] lemma tilt_zero (μ : Measure α) [IsProbabilityMeasure μ] (H : α → ℝ) (x : α) :
    tilt μ H 0 x = 1 := by simp [tilt]

end Gibbs
end YM.Push.BetaTransport
