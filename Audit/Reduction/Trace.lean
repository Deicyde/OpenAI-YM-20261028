import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The trace test only reads the selected phase, which is `T₀`'s selected phase. -/
theorem reduced_trace {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure)
    (hT : T₀.TraceTest) : (reduced T₀ μ hH).TraceTest := by
  have htwo : (reduced T₀ μ hH).traceTwo = T₀.traceTwo := by
    funext r
    simp only [Hierarchy.traceTwo, reduced, redCorrelation, ↓reduceIte]
  refine ⟨fun f => hT.centered f, hT.amplitudePositive, ?_, ?_⟩
  · rw [htwo]; exact hT.shortDistance
  · intro terms; rw [htwo]; exact hT.excludes terms

end YMAudit
