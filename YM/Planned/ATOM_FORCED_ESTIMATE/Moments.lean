import YM.Planned.ATOM_FORCED_ESTIMATE.Held

/-! Moment comparisons for cost tests on returning from the held kernel, keeping
all partner moments on the **same** law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.Forced.Moment
open MeasureTheory Function Filter
open scoped ENNReal NNReal Topology BigOperators
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {a b : ℝ}

/-- Nonnegative majorant in power norm on a common measure. -/
structure Power (μ : Measure α) (k : ℕ) (f : α → ℝ) (a : ℝ) : Prop where
  price : 0 ≤ a
  positive : 0 ≤ᵐ[μ] f
  meas : AEStronglyMeasurable f μ
  integrable : Integrable (fun x => f x ^ k) μ
  moment : (∫ x, f x ^ k ∂μ) ≤ a ^ k

namespace Power










end Power
end YM.Planned.Forced.Moment
