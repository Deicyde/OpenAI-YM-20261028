import YM.SectorNext.VACUUM_NORMALIZATION.Gas

/-!
# The pinned numerator

One species can report many distinct tokens (including, later, fine sorts of
seeds with coincident projections, coarse flags, and marker slots). If two
species report the same token they are incompatible. Requests have two modes:
`hard` means presence must agree *exactly* with the request, others may be
reported without having been requested. We do **not** set unrequested optional
tokens to zero when comparing to the vacuum.

This is a utility for the estimate on the actual density. Use any `∑'` in this
development with summability. We don't claim an identity of sectors from
combinatorics alone.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp
open Finset Function Filter
open SectorNext.Vacuum.ReLog
open scoped Topology BigOperators Classical

variable {J ι E : Type*} [Fintype J] [DecidableEq J] [DecidableEq E]

/-- `J`: physical output sites; `ι`: species; `E`: individual token tests. -/
structure Claims (J ι E : Type*) where
  supp : ι → Leaf J
  full (i : ι) : (supp i).Nonempty
  tokens : ι → Finset E
  loc : E → J
  binds (i : ι) (e : E) : e∈tokens i → loc e ∈ supp i

namespace Claims

variable (M : Claims J ι E) (hard s : Finset E) (u : ι → ℝ) (B : Leaf J)

def found (P : Finset ι) : Finset E := P.biUnion M.tokens

def Needed (P : Finset ι) := s ⊆ M.found P ∧ hard ∩ M.found P ⊆ s

















-- Use arbitrary finite label truncation.
def permitted (I : Finset ι) : Finset (Finset ι) := (accepted M.supp B I).filter (M.Needed hard s)







private lemma drop (i : ι) (I : Finset ι) (P : Finset ι)
    (hi : i∈I) (hX : M.supp i ⊆ B) (he : hard ∩ M.tokens i ⊆ s) (hh : i ∉ P) :
    insert i P ∈ M.permitted hard s B I ↔
      P ∈ M.permitted hard (s \ M.tokens i) (B \ M.supp i) I := by
  simp only [permitted,mem_filter]
  rw [extend_stays M.supp B I i hi hX P hh]
  apply and_congr_right
  intro hP
  have hz : Disjoint (M.tokens i) (M.found P) := Finset.disjoint_left.mpr (fun t ht ha => by
    obtain ⟨j,hj,hk⟩ := mem_biUnion.mp ha
    exact (mem_sdiff.mp (((accepts ..).mp hP).2.1 j hj (M.binds j t hk))).2 (M.binds i t ht))
  have h₂ : M.found (insert i P)= M.tokens i ∪ M.found P := by ext; simp [found]
  unfold Needed; rw [h₂]
  constructor
  · rintro ⟨h₁,h₂⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · obtain ⟨he',hh⟩ := mem_sdiff.mp ht
      exact (mem_union.mp (h₁ he')).resolve_left hh
    obtain ⟨he',hh'⟩ := mem_inter.mp ht
    exact mem_sdiff.mpr ⟨h₂ (mem_inter.mpr ⟨he', mem_union_right _ hh'⟩),
      fun ht => Finset.disjoint_left.mp hz ht hh'⟩
  rintro ⟨h₁,h₂⟩
  refine ⟨fun t ht => ?_,fun t ht => ?_⟩
  · by_cases ha : t∈ M.tokens i
    · exact mem_union_left _ ha
    exact mem_union_right _ (h₁ (mem_sdiff.mpr ⟨ht,ha⟩))
  obtain ⟨ha,hb⟩ := mem_inter.mp ht
  rcases mem_union.mp hb with h|h
  · exact he (mem_inter.mpr ⟨ha,h⟩)
  exact (mem_sdiff.mp (h₂ (mem_inter.mpr ⟨ha,h⟩))).1





end Claims
end YM.AnalyticBridge.Sharp
