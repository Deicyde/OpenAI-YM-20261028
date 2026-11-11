import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The reduced hierarchy satisfies `Reconstructed`: the selected-phase clauses are `T₀`'s,
and the two phases average to the Wilson limit `allZero`. -/
theorem reduced_reconstructed {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure)
    (hR : T₀.Reconstructed) : (reduced T₀ μ hH).Reconstructed := by
  sorry

end YMAudit
