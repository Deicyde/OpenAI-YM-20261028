import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Every gauge group carries a Haar probability measure (for the Borel structure declared
in `PublicWilson`). -/
theorem exists_haar (g : GaugeGroup) :
    ∃ μ : Measure g.image, IsProbabilityMeasure μ ∧ μ.IsHaarMeasure := by
  sorry

end YMAudit
