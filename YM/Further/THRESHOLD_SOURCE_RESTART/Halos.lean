import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
/-!
# Same lattice, narrower threshold 

Even before integrating, an occurrence in the new-threshold restart may
need old final flags. Convert stencils and still pay the extra hit possible
inside *inspection*. (Can't claim they're local just on the old numerical
sites!) B bigger than the old B in this use. Weaker than traversing for a
1/B exponent gain; account allowance accordingly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Halos
open Function Set Relation Filter MeasureTheory Wilson RG Lattice Lattice.Corona Marker Overlay
open Push.Corrected Prepare Width Extra.Multi Ac
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {α : Type*} {n : Side} {Y : Support n} {X : α → Support n}
variable {M B : ℕ} {a b c : ℝ} {f : α → ℝ}

theorem enters : Y ⊆ inspected Y := Finset.subset_union_left
theorem at_old {x : Site n} (h : x∈inspected Y) : ∃ y∈Y,separation y x ≤ 4 := by
  rcases Finset.mem_union.mp h with he|he
  · exact ⟨x,he,by simp⟩
  obtain ⟨q,-,hq⟩ := Finset.mem_biUnion.mp he
  split at hq; next h => simp at hq
  next h =>
    obtain ⟨y,h1,h2⟩ := Finset.not_disjoint_iff.mp h
    have ht := Work.E01.sep_touched q x hq; have hg := Work.E01.sep_touched q y h2
    exact ⟨y,h1,(separation_triangle y q.1 x).trans (by rw [separation_comm y]; omega)⟩




end YM.Further.ThresholdSourceRestart.Halos
