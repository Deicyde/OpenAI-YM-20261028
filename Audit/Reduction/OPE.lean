import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The reduced hierarchy has an all-orders OPE with shared coefficients in every phase. -/
theorem reduced_ope {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure)
    (hO : T₀.OperatorProductExpansion) (hZ : ZeroInvisible T₀) :
    (reduced T₀ μ hH).OperatorProductExpansion := by
  sorry

end YMAudit
