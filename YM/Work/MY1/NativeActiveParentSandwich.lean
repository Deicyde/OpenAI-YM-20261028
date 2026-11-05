import YM.Work.E03
import YM.Work.MY3ActiveGeometry


/-!
The native active mask tests both projected endpoints, whereas the donor
component mask tests only the projected stem.  These masks are not identified.
The stem mask outside the (10B+1)-halo is contained in the actual active mask,
which is contained in the stem mask outside the 10B-halo.  Their difference is
therefore confined to the one-layer coarse boundary, including on a torus.

This supplies geometry for a component re-disintegration.  It does not assert
that the boundary coordinates have zero cost, the same conditional covariance,
or a controlled weighted integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.MY1.NativeActiveParentSandwich

open Lattice Wilson RG Tree Pressure
open MY3ActiveGeometry
open scoped Classical

variable {G : Gauge} {c f : Side}

/-- Free links selected by the projected stem alone, on the original forest. -/
def stemFree (S : StepData c f) (F : Forest S.ratio) (V : Config G c)
    (x : ℝ) (choice : MY3SmoothSeedSectors.Choices c f) (r : ℕ) : Finset F.Free :=
  Finset.univ.filter fun e =>
    S.ratio.parent e.val.1 ∉ halo r (seedSites S V x choice)

@[simp] theorem mem_stemFree (S : StepData c f) (F : Forest S.ratio)
    (V : Config G c) (x : ℝ) (choice : MY3SmoothSeedSectors.Choices c f)
    (r : ℕ) (e : F.Free) :
    e ∈ stemFree S F V x choice r ↔
      S.ratio.parent e.val.1 ∉ halo r (seedSites S V x choice) := by
  simp only [stemFree, Finset.mem_filter, Finset.mem_univ, true_and]

/-- An end in the original halo puts the stem in its one-layer enlargement. -/
theorem end_near_stem_enlarged (S : StepData c f) (V : Config G c)
    (x : ℝ) (choice : MY3SmoothSeedSectors.Choices c f) (e : Bond f)
    (he : S.ratio.parent (e.1 + step e.2) ∈ nearSeedSites S V x choice) :
    S.ratio.parent e.1 ∈ halo (10 * radiusB x + 1) (seedSites S V x choice) := by
  change S.ratio.parent (e.1 + step e.2) ∈
    halo (10 * radiusB x) (seedSites S V x choice) at he
  obtain ⟨y, hy, hd⟩ := halo_spec.mp he
  apply halo_spec.mpr
  refine ⟨y, hy, ?_⟩
  have hs : separation (S.ratio.parent (e.1 + step e.2))
      (S.ratio.parent e.1) ≤ 1 := by
    rw [separation_comm]
    exact YM.Work.E03.parent_step S e.1 e.2
  exact (separation_triangle y (S.ratio.parent (e.1 + step e.2))
    (S.ratio.parent e.1)).trans (Nat.add_le_add hd hs)



theorem stemFree_succ_subset_activeFree (S : StepData c f) (F : Forest S.ratio)
    (V : Config G c) (x : ℝ) (choice : MY3SmoothSeedSectors.Choices c f) :
    stemFree S F V x choice (10 * radiusB x + 1) ⊆ activeFree S F V x choice := by
  intro e he
  have hfar := (mem_stemFree S F V x choice _ e).mp he
  apply (mem_activeFree S F V x choice e).mpr
  apply (mem_activeLinks S F V x choice e.val).mpr
  refine ⟨e.property, ?_⟩
  intro hn
  rcases hn with hs | ht
  · apply hfar
    obtain ⟨y, hy, hd⟩ := halo_spec.mp hs
    exact halo_spec.mpr ⟨y, hy, hd.trans (Nat.le_succ _)⟩
  · exact hfar (end_near_stem_enlarged S V x choice e.val ht)



/-- No discrepancy is silently discarded: every differing coordinate remains
in the explicit one-layer stem boundary. -/
theorem stem_difference_subset_boundary (S : StepData c f) (F : Forest S.ratio)
    (V : Config G c) (x : ℝ) (choice : MY3SmoothSeedSectors.Choices c f) :
    stemFree S F V x choice (10 * radiusB x) \ activeFree S F V x choice ⊆
      stemFree S F V x choice (10 * radiusB x) \
        stemFree S F V x choice (10 * radiusB x + 1) := by
  intro e he
  obtain ⟨hs, hnot⟩ := Finset.mem_sdiff.mp he
  exact Finset.mem_sdiff.mpr ⟨hs, fun h =>
    hnot (stemFree_succ_subset_activeFree S F V x choice h)⟩

end YM.Work.MY1.NativeActiveParentSandwich
