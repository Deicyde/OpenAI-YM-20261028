import HierarchyBridge
import YM.TraceExtension.Wick.Refute

set_option autoImplicit false
noncomputable section
namespace YangMills
open YM YM.Spec YM.OPE.Orbits YM.Nonperturbative YM.TraceExtension
open Function Set MeasureTheory Filter
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius NNReal
universe u v
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

private def nativeMode (m : Hierarchy.Mode) : Wick.Mode :=
  ⟨m.mass,m.spatialOrder,m.timeOrder,m.numerator,m.continuous,m.homogeneous⟩
private def nativeTrack (t : Hierarchy.Track) : Wick.Track := ⟨t.n,nativeMode ∘ t.modes⟩
private def nativeTerms (t : List (ℂ × Hierarchy.Track)) : Wick.Collection :=
  t.map fun (c,q) => (c,nativeTrack q)
private theorem profile_eq (t : List (ℂ × Hierarchy.Track)) (r : ℝ) :
    Hierarchy.wickProfile t r = Wick.atPoint (nativeTerms t) r := by
  unfold Hierarchy.wickProfile Wick.atPoint nativeTerms
  rw [List.map_map]
  congr 1
private theorem award_eq (hg : g.IsSimple) :
    YM.Trace.Verse.award g.core = 3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi^4 := by
  have h : g.core.lie = g.lieAlgebra := by ext v; exact (g.generates v).symm
  have dim : g.core.lieDim = Module.finrank ℝ g.lieAlgebra := congrArg (fun V : Submodule ℝ (Matrix (Fin (g.n+1)) (Fin (g.n+1)) ℂ) => Module.finrank ℝ V) h
  have hc := YM.Gauge.casimir_pos (G := g.core) (GaugeGroup.coreSimple hg)
  unfold YM.Trace.Verse.award
  rw [dim]
  unfold YM.Trace.Over.d2 YM.Trace.Over.b0 YM.Trace.Over.forceR YM.Gauge.slopeConstant
  field_simp [ne_of_gt hc, Real.pi_ne_zero]
  ring

theorem publicTrace (hg : g.IsSimple) (H : Headline.TraceExclusions.{u,v} F) :
    (hierarchy F Q).TraceTest := by
  have ht : (hierarchy F Q).traceTwo = euclidean F := rfl
  refine ⟨H.centered, (award_eq hg) ▸ H.positive, ?_, ?_⟩
  · rw [ht,← award_eq hg]
    exact H.shortDistance
  · intro terms e
    apply Wick.euclidean_excludes (F := F) H.shortDistance H.positive (nativeTerms terms)
    filter_upwards [e] with r hr
    exact (congrFun ht r).symm.trans (hr.trans (profile_eq terms r))
end YangMills
