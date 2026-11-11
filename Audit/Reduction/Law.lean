import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The normalized Wilson law is a probability measure. -/
theorem wilsonLaw_isProbability (g : GaugeGroup) (l : ℕ+) (β : ℝ) (μ : Measure g.image)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (wilsonLaw g l β μ) := by
  sorry

/-- Finite moments of the gauge-blind family are the indicator `allZero`. -/
theorem blind_finiteMoment {g : GaugeGroup} (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (F : ℕ → Type) [∀ d, Zero (F d)] (N p : ℕ) {n : ℕ}
    (v : Fin n → Σ d, F d)
    (x : Fin n → Site ((blindFamily μ hH F).period p * (blindFamily μ hH F).denominator N)) :
    (blindFamily μ hH F).finiteMoment N p v x = allZero v := by
  sorry

end YMAudit
