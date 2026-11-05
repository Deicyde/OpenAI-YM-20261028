import YM.MultiNext.VACUUM_STABILITY.Alternatives
import YM.Work.B04

set_option warningAsError false

/-!
# Restore exclusions of forced packs

Output of first system includes a list of disjoint forced species with full coverage. Their
exclusion of unforced letters means restoring exactly those NEGATIVE clusters meeting the
original d-family. Furthermore other flag-hitting corrections in the scalar exponent meet the
d-family by coverage. Gather these using ONE alphabet and ONE overlap on complete supports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Rejoin
open RG Lattice Wilson Filter Finset Function MeasureTheory Text  Syllable Corona Alternatives
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I J : Type*} {n : Side}

/-- K species at original Packs. Optional exponent letters, using all their
addresses, at nonempty supports (caller fits final flag-read convention). -/
structure Hearth (n : Side) (I J : Type*) where
  pack : I → Multi.Pack n
  sites : J → Support n
  ample i : (sites i).Nonempty

namespace Hearth
variable (D : Hearth n I J)

abbrev Color (I J : Type*) := I ⊕ Choices J
abbrev Lot (I J : Type*) := Finset (Color I J)

def span : Color I J → Support n := Sum.elim (fun i => (D.pack i).zone) (fun j => D.sites j.1)

def ground (b : Lot I J) := b.biUnion D.span
def tags (b : Lot I J) := b.toLeft.biUnion (fun i => (D.pack i).flagsAt)





def aimed (s : Finset I) (i : J) := ∃ k∈s, ¬ Disjoint (D.sites i) (D.pack k).zone

structure FamilyPass (b : Lot I J) : Prop where
  wins : (b.toLeft : Set I).PairwiseDisjoint (fun i => (D.pack i).zone)
  once : Set.InjOn (Prod.fst : Choices J → J) (b.toRight:Set (Choices J))
  owed : ∀ i ∈ b.toRight, D.aimed b.toLeft i.1



def belongs (b : Lot I J) := b.toLeft.Nonempty ∧ Ac.Spark D.span b ∧ D.FamilyPass b
abbrev Piece := {b : Lot I J // D.belongs b}

/-- complete new support after the merger -/
def remap (v : Piece D) : Multi.Pack n := by
  refine ⟨⟨D.ground v.val,D.tags v.val⟩, ?_,?_⟩
  · obtain ⟨i,hi⟩ := v.property.1; obtain ⟨x,hx⟩ := (D.pack i).property.1
    exact ⟨x, Finset.mem_biUnion.mpr ⟨i,hi,hx⟩⟩
  intro i hi; obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hi
  exact mem_biUnion.mpr ⟨Sum.inl j, Finset.mem_toLeft.mp hj,(D.pack j).property.2 hx⟩

lemma remap_zone (v : D.Piece) : (D.remap v).zone = D.ground v.val := rfl
lemma remap_tags (v : D.Piece) : (D.remap v).flagsAt = D.tags v.val := rfl




















end Hearth
end YM.Multi.Vacuum.Rejoin
