import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The unitary group of `k × k` complex matrices is a compact subset of the matrices: it is
closed, and every entry of a unitary matrix lies in the closed unit ball of `ℂ`. -/
theorem isCompact_unitaryGroup (k : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  refine (IsCompact.matrix (isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset
    isClosed_unitary ?_
  intro U hU i j
  simpa using entry_norm_bound_of_unitary hU i j

/-- The image of a gauge group is a compact space (a closed subgroup of the compact unitary
group). -/
theorem compactSpace_image (g : GaugeGroup) : CompactSpace g.image := by
  haveI : CompactSpace (UnitaryRepresentation g.n) :=
    isCompact_iff_compactSpace.mp (isCompact_unitaryGroup (g.n + 1))
  exact isCompact_iff_compactSpace.mp g.imageClosed.isCompact

/-- Every gauge group carries a Haar probability measure (for the Borel structure declared
in `PublicWilson`). -/
theorem exists_haar (g : GaugeGroup) :
    ∃ μ : Measure g.image, IsProbabilityMeasure μ ∧ μ.IsHaarMeasure := by
  haveI := compactSpace_image g
  refine ⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance⟩
  have h := Measure.haarMeasure_self (G := g.image) (K₀ := ⊤)
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h

end YMAudit
