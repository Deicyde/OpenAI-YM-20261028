import YM.Next.EXTRACTION.Tails
import YM.Work.A15
import YM.Work.B04


/-!
# Bounded real β weights and Bochner insertions

Helpers for the finite probability Haar integrals, not hypotheses about the RG map.
Neighborhoods for the common dominating functions and derivative tests are uniform
in the integration variable. All derivatives here and in clients are for a *real*
parameter, including when fields/coefficients are complex.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Push.BetaTransport
open Filter MeasureTheory Set
open scoped Topology

variable {α : Type*} [MeasurableSpace α]

lemma eventually_abs_bound (β : ℝ) : {b | |b| ≤ |β| + 1} ∈ 𝓝 β :=
  continuous_abs.continuousAt.tendsto.eventually (eventually_le_nhds (lt_add_one |β|))

/-- No control of branch variation in α by topology is used here. -/
structure WeightEstimate (w w' : ℝ → α → ℝ) (A : ℝ) (C : ℝ → ℝ) : Prop where
  measurable (β : ℝ) : Measurable (w β)
  measurable' (β : ℝ) : Measurable (w' β)
  nonneg (β : ℝ) (x : α) : 0 ≤ w β x
  le {β R : ℝ} (h : |β| ≤ R) (x : α) : w β x ≤ C R
  slope (β : ℝ) (x : α) : ‖w' β x‖ ≤ A * w β x
  has (β : ℝ) (x : α) : HasDerivAt (w · x) (w' β x) β
  cap : 0 ≤ A
  capWeight (R) : 0 ≤ R → 0 ≤ C R

namespace WeightEstimate
variable {w w' v v' : ℝ → α → ℝ} {A B : ℝ} {C D : ℝ → ℝ}

lemma comp {γ : Type*} [MeasurableSpace γ] (h : WeightEstimate w w' A C) {f : γ → α}
    (hf : Measurable f) : WeightEstimate (fun β x => w β (f x)) (fun β x => w' β (f x)) A C :=
  ⟨fun β => (h.measurable β).comp hf, fun β => (h.measurable' β).comp hf,
    fun _ _ => h.nonneg ..,fun hx _ => h.le hx _, fun _ _ => h.slope ..,fun _ _ => h.has ..,
    h.cap,h.capWeight⟩



variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {μ : Measure α}

lemma smul_integrable (h : WeightEstimate w w' A C) (β : ℝ) {F : α → X} (hf : Integrable F μ) :
    Integrable (fun x => w β x • F x) μ :=
  hf.bdd_smul _ (h.measurable β).aestronglyMeasurable (Eventually.of_forall fun x =>
    (Real.norm_of_nonneg (h.nonneg β x)).trans_le (h.le le_rfl x))

lemma slope_integrable (h : WeightEstimate w w' A C) (β : ℝ) {F : α → X} (hf : Integrable F μ) :
    Integrable (fun x => w' β x • F x) μ :=
  hf.bdd_smul _ (h.measurable' β).aestronglyMeasurable (Eventually.of_forall fun x =>
    (h.slope β x).trans (mul_le_mul_of_nonneg_left (h.le le_rfl x) h.cap))

variable [CompleteSpace X]
-- Keep completeness to avoid interpreting integral_undef as a Bochner integral.
set_option linter.unusedSectionVars false

lemma norm_integral_le (h : WeightEstimate w w' A C) (β : ℝ) {F : α → X} (_ : Integrable F μ) :
    ‖∫ x, w β x • F x ∂μ‖ ≤ ∫ x, w β x * ‖F x‖ ∂μ := by
  simpa only [norm_smul,Real.norm_of_nonneg (h.nonneg _ _)] using
    norm_integral_le_integral_norm (μ := μ) (fun x => w β x • F x)

lemma slope_integral_le (h : WeightEstimate w w' A C) (β : ℝ) {F : α → X} (hf : Integrable F μ) :
    ‖∫ x, w' β x • F x ∂μ‖ ≤ A * ∫ x, w β x * ‖F x‖ ∂μ := by
  rw [← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono ((h.slope_integrable β hf).norm)
    ((h.smul_integrable β hf.norm).const_mul _) fun x => ?_)
  rw [norm_smul,← mul_assoc]; exact mul_le_mul_of_nonneg_right (h.slope ..) (norm_nonneg _)

/-- Constant (in β) but otherwise arbitrary integrable insertion. -/
lemma integral_derivative (h : WeightEstimate w w' A C) {F : α → X} (hf : Integrable F μ) (β : ℝ) :
    HasDerivAt (fun b => ∫ x, w b x • F x ∂μ) (∫ x, w' β x • F x ∂μ) β := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F':=fun b x => w' b x • F x)
    (eventually_abs_bound β) (Eventually.of_forall fun b => (h.smul_integrable b hf).1)
    (h.smul_integrable β hf) (h.slope_integrable β hf).1 (Eventually.of_forall fun x b hb => ?_)
    (hf.norm.const_mul (A*C (|β|+1))) (Eventually.of_forall fun x b _ => (h.has b x).smul_const _)).2
  rw [norm_smul]; gcongr
  exact (h.slope ..).trans (mul_le_mul_of_nonneg_left (h.le hb x) h.cap)



end WeightEstimate
end YM.Push.BetaTransport
