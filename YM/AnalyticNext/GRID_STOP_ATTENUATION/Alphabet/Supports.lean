import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Next.MULTISOURCE.Curves
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04

set_option warningAsError false

/-!
# Repacketizing one forced insertion -- exact geometry, no normalization

An exact transformation useful around compatibility requirements and for
investigating rigidity/obstructions for `Stepwise`.

It generally can't just
be done on each entry of an ARRAY independently (since it's multiplying into
the unmarked gas and editing supports).

Here only change
support of a marked Pulse contribution, before final allocation with Room,
never any incumbent address.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Alphabet
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Multi.Pack
open Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {n : Side}

section outside
variable {α : Type*} [CommSemiring α]

def listed (D : Support n) (p : Pack n) (x : Finset (Pack n)) :=
    (x:Set (Pack n)).PairwiseDisjoint zone ∧ (∀ i∈x, Disjoint i.zone p.zone) ∧ p.flagsAt ∪ x.biUnion flagsAt = D

-- contribution of an insertion at this Pack (without its D yet)
def shells (F : Pack n → α) (L : Finset (Pack n)) := ∏ i∈L,F i
def diamond (D : Support n) (F : Pack n→α) (i : Pack n) := ∑ t : Finset (Pack n), if listed D i t then shells F t else 0

private lemma grown (p : Pack n) : p.zone.Nonempty := p.property.1.mono p.property.2
private lemma apart_ne (i j : Pack n) (h : Disjoint i.zone j.zone) : i ≠ j := by
  rintro rfl; obtain ⟨x,hx⟩ := grown i; exact disjoint_left.mp h hx hx

lemma lit (D : Support n) (p : Pack n) (x : Finset (Pack n)) : listed D p x ↔ (insert p x∈clears D ∧ p∉x) := by
  unfold listed clears; simp only [mem_filter,mem_univ,true_and, Finset.biUnion_insert, Finset.coe_insert, Set.pairwiseDisjoint_insert,and_assoc]
  constructor
  · rintro ⟨hT,hI,hh⟩
    exact ⟨hT,fun i hi _ => (hI i hi).symm,hh,fun he => apart_ne _ _ (hI p he) rfl⟩
  rintro ⟨hT,hI,hh,hx⟩
  refine ⟨hT,fun i hi => (hI i hi (fun he => hx (he ▸ hi))).symm,hh⟩

lemma lit_at (D : Support n) (p : Pack n) (x : Finset (Pack n)) (h : listed D p x) : p.zone ∩ D=p.flagsAt := by
  apply le_antisymm <;> intro i hi
  · obtain ⟨h1,h2⟩ := mem_inter.mp hi; rw [← h.2.2] at h2; obtain hi|hi := mem_union.mp h2
    · exact hi
    obtain ⟨j,hj,hg⟩ := mem_biUnion.mp hi
    exact False.elim (disjoint_left.mp (h.2.1 j hj) (j.property.2 hg) h1)
  rw [← h.2.2]; exact mem_inter.mpr ⟨p.property.2 hi,mem_union_left _ hi⟩

lemma diamond_guard (D : Support n) (F : Pack n → α) (p : Pack n) (h : p.zone ∩ D ≠ p.flagsAt) : diamond D F p=0 := by
  unfold diamond; exact Finset.sum_eq_zero fun j _ => if_neg (fun he => h (lit_at D p j he))

variable (D : Support n) (F : Pack n → α) (i p : Pack n)

def spread (z : Site n) : Pack n :=
    ⟨⟨insert z p.zone,p.flagsAt⟩,p.property.1,p.property.2.trans (subset_insert ..)⟩

def braid (j : Pack n) : Pack n :=
    ⟨⟨p.zone ∪ j.zone,p.flagsAt ∪ j.flagsAt⟩,p.property.1.mono subset_union_left,
      union_subset_union p.property.2 j.property.2⟩

def attaches (z : Site n) : Finset (Pack n) := univ.filter fun i : Pack n => z∈i.zone ∧ Disjoint i.zone p.zone

lemma spread_legal (z : Site n) (x : Finset (Pack n)) : listed D (spread p z) x ↔
    listed D p x ∧ ∀ i∈ x,z∉ i.zone := by
  unfold listed; constructor
  · rintro ⟨hx,hv,he⟩; change ∀ i∈x,Disjoint i.zone (insert z p.zone) at hv
    exact ⟨⟨hx,fun i hi => (hv i hi).mono_right (subset_insert ..), he⟩,fun i hi hh => disjoint_left.mp
      (hv i hi) hh (mem_insert_self ..)⟩
  rintro ⟨⟨hx,hv,he⟩,h⟩
  refine ⟨hx,fun i hi => ?_,he⟩
  change Disjoint _ (insert z p.zone); rw [Finset.disjoint_insert_right]; exact ⟨h i hi,hv i hi⟩

lemma braid_legal (j : Pack n) (x : Finset (Pack n)) (he : Disjoint j.zone p.zone) :
    listed D (braid p j) x ↔ listed D p (insert j x) ∧ j∉x := by
  unfold listed; simp only [Finset.biUnion_insert,Finset.coe_insert,Set.pairwiseDisjoint_insert]
  constructor
  · rintro ⟨hx,hi,h⟩
    change ∀ i∈x,Disjoint i.zone (p.zone ∪ j.zone) at hi
    refine ⟨⟨⟨hx,fun i hv _ => ((hi _ hv).mono_right subset_union_right).symm⟩,fun i hh => ?_,?_⟩,fun H => ?_⟩
    · rcases mem_insert.mp hh with H|H
      · exact H ▸ he
      exact (hi _ H).mono_right subset_union_left
    · change (_ ∪ _)∪ _ = D at h
      rwa [union_assoc] at h
    exact apart_ne _ _ ((hi j H).mono_right subset_union_right) rfl
  rintro ⟨⟨⟨hx,hj⟩, hi,h⟩,hr⟩
  refine ⟨hx,?_,?_⟩
  · intro t ht; change Disjoint _ (p.zone ∪ j.zone); rw [Finset.disjoint_union_right]
    exact ⟨hi t (mem_insert_of_mem ht),(hj t ht (fun e => hr (e ▸ ht))).symm⟩
  change (_∪_)∪_=_; rwa [union_assoc]

/-- Partition all outsider constellations into z-vacant or unique z-hosted.
Also works when p was already reading z (then hosted correction vacuous).
-/
theorem diamond_step (z : Site n) : diamond D F p=diamond D F (spread p z) +
    ∑ j∈attaches p z, F j * diamond D F (braid p j) := by
  let J := attaches p z
  let f (j : Finset (Pack n)) := if listed D p j then shells F j else 0
  have he (L : Finset (Pack n)) : (if listed D p L then shells F L else 0) =
      (if listed D (spread p z) L then shells F L else 0)+∑ j∈J, if j∈L then f L else 0 := by
    by_cases H : listed D p L
    · rw [if_pos H,spread_legal, show (listed D p L ∧ ∀ i∈L,z∉i.zone) ↔ (∀ i∈L,z∉i.zone) by simp [H]]
      split
      next h =>
        rw [Finset.sum_eq_zero ?_,add_zero]; intro i hi
        exact if_neg (fun H => h _ H (mem_filter.mp hi).2.1)
      next h =>
        push Not at h; obtain ⟨j,hj,he⟩ := h
        rw [zero_add,Finset.sum_eq_single j]
        · rw [if_pos hj]; exact (if_pos H).symm
        · intro i hi hh; exact if_neg (fun hI => disjoint_left.mp (H.1 hI hj hh) (mem_filter.mp hi).2.1 he)
        exact fun h => False.elim (h (mem_filter.mpr ⟨mem_univ _,he,H.2.1 j hj⟩))
    rw [if_neg H,if_neg (fun h => H ((spread_legal D p z L).mp h).1)]
    unfold f; simp [H]
  unfold diamond
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_comm (s:=univ) (t:=J)]
  refine congrArg (_ + ·) ?_
  refine sum_congr rfl fun i hi => ?_
  have h := (mem_filter.mp hi).2.2
  have hv : ((attaches p z):Finset (Pack n))=J := rfl
  rw [Finset.mul_sum]; have hF : (∑ x : Finset (Pack n), if i∈x then f x else 0) = ∑ x∈univ.filter (fun x : Finset (Pack n) => i∈x),f x := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun j _ => by split <;> rfl
  rw [hF]
  let g (x) := if listed D (braid p i) x then shells F x else 0
  have hS : (∑ x : Finset (Pack n),F i*g x)=∑ x ∈ univ.filter (fun x : Finset (Pack n) => i ∉ x), F i*g x := by
    apply Eq.symm
    refine sum_subset (subset_univ _) fun j _ hj => ?_
    have HT : i∈j := by simpa using hj
    unfold g; rw [if_neg (fun e => (braid_legal D p i j h).mp e |>.2 HT),mul_zero]
  change _ = ∑ x,F i*g x; rw [hS]
  symm; refine sum_bij (fun j _ => insert i j) ?_ ?_ ?_ ?_
  · intro j _; simp
  · intro a ha b hb H; simpa [(mem_filter.mp ha).2,(mem_filter.mp hb).2] using congr_arg (Finset.erase · i) H
  · intro b hb; exact ⟨b.erase i,by simp,Finset.insert_erase ((mem_filter.mp hb).2)⟩
  intro a ha; have hh := (mem_filter.mp ha).2
  unfold g f; rw [braid_legal _ p i _ h]; simp only [hh,not_false_eq_true,and_true]
  unfold shells; split
  · simp only [prod_insert hh]
  simp only [mul_zero]
end outside
end YM.AnalyticNext.GridStop.Alphabet
