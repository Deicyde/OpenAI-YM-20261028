import Mathlib.RingTheory.Nilpotent.Exp
import YM.Next.EXTRACTION.Tails

/-!
# Interpolation trees over actual marker sets

When writing a term on `T,A`, `A` is the progenitor block (one root,
possibly a number of labels already fused). At the full coefficient with
`A={i}`, these are ordinary rooted labelled spanning trees. Each vertex in
`T \\ A` specifies one edge to its parent. No hidden sum over attachment
orders in the budget using these trees -- those are integrated away.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
namespace Grove
open Function Finset
open scoped BigOperators
variable {V : Type} [DecidableEq V]

/-- Parent map (elsewhere fixed). -/
abbrev Parent (V : Type) := V → V

/-- Rooted on `A`. Use the no-cycle test even if marker positions coincide. -/
structure Good (T A : Finset V) (f : Parent V) : Prop where
  goes i (h : i ∈ T \ A) : f i ∈ T
  out i (h : i∉T \ A) : f i=i
  finite (s : Finset V) (h : s⊆T \ A) (he : s.Nonempty) : ∃ i ∈ s,f i∉s

/-- Frontier already incident to root block. -/
def buds (T A : Finset V) (f : Parent V) := (T \ A).filter fun j => f j ∈ A

def cut (f : Parent V) (j : V) := update f j j

def join (f : Parent V) (j i : V) := update f j i

variable {T A : Finset V} {f : Parent V} {i j : V}
lemma Buds.kids (h : j ∈ buds T A f) : j ∈ T \ A := (mem_filter.mp h).1
lemma Buds.roots (h : j ∈ buds T A f) : f j∈A := (mem_filter.mp h).2

lemma Good.buds (h : Good T A f) (he : (T \ A).Nonempty) : (Grove.buds T A f).Nonempty := by
  obtain ⟨i,hi,hj⟩ := h.finite (T \ A) Subset.rfl he
  have hx := h.goes i hi
  exact ⟨i,mem_filter.mpr ⟨hi,not_not.mp fun ht => hj (mem_sdiff.mpr ⟨hx,ht⟩)⟩⟩



lemma leaves (T A : Finset V) (j : V) : T \ insert j A = (T \ A).erase j := by
  ext; simp [and_left_comm]

lemma Good.cut_at (h : Good T A f) (_hj : j∈T \ A) : Good T (insert j A) (cut f j) := by
  constructor
  · intro i he
    rw [leaves] at he; rw [cut,update_of_ne (ne_of_mem_erase he)]; exact h.goes i (mem_of_mem_erase he)
  · intro i he
    by_cases hi : i=j
    · rw [hi,cut,update_self]
    rw [cut,update_of_ne hi]; apply h.out
    intro hf; exact he (by rw [leaves]; exact mem_erase.mpr ⟨hi,hf⟩)
  intro s hs he
  rw [leaves] at hs
  obtain ⟨i,hi,hj⟩ := h.finite s (hs.trans (erase_subset ..)) he
  exact ⟨i,hi,by rw [cut,update_of_ne (ne_of_mem_erase (hs hi))]; exact hj⟩

lemma Good.join_at (h : Good T (insert j A) f) (ha : A⊆T) (hj : j∈T \ A) (hi : i∈A) :
    Good T A (join f j i) := by
  constructor
  · intro k hk; by_cases he : k=j
    · rw [he,join,update_self]; exact ha hi
    rw [join,update_of_ne he]; apply h.goes
    rw [leaves]; exact mem_erase.mpr ⟨he,hk⟩
  · intro k hk
    rw [join,update_of_ne (by intro he; exact hk (he ▸ hj))]; apply h.out
    rw [leaves]; exact fun he => hk (mem_of_mem_erase he)
  intro s hs hn
  by_cases he : j∈s
  · refine ⟨j,he,?_⟩; rw [join,update_self]; intro hc; exact (mem_sdiff.mp (hs hc)).2 hi
  obtain ⟨k,hk,hb⟩ := h.finite s (by rw [leaves]; exact subset_erase.mpr ⟨hs,he⟩) hn
  exact ⟨k,hk,by rw [join,update_of_ne (by intro hi; exact he (hi ▸ hk))]; exact hb⟩

lemma join_cut (f : Parent V) (j : V) : join (cut f j) j (f j)=f := by simp [join,cut]
lemma Good.cut_join (h : Good T (insert j A) f) (i : V) : cut (join f j i) j=f := by
  have he : f j=j := h.out j (by simp)
  unfold cut join; rw [update_idem]; exact funext fun k => by
    by_cases ht : k=j
    · rw [ht,update_self,he]
    rw [update_of_ne ht]

/-- Degree at i. With multiple roots in A, charge their individual
valencies in this extension (A-internal edges not charged twice). -/
def deg (T A : Finset V) (f : Parent V) (i : V) := ((T\A).filter fun j => f j=i).card +
    if i∈T\A then 1 else 0

lemma degrees (h : j∈buds T A f) (i : V) : deg T A f i = deg T (insert j A) (cut f j) i +
    (if i=j then 1 else 0)+(if i=f j then 1 else 0) := by
  let s := T\A
  have hj : j∈s := Buds.kids h
  have he : ((s.erase j).filter fun k => cut f j k=i) =
      ((s.erase j).filter fun k => f k=i) := by
    apply filter_congr; intro k hk; rw [cut,update_of_ne (ne_of_mem_erase hk)]
  have hb : (s.filter fun k => f k=i).card=((s.erase j).filter fun k => f k=i).card+
      (if i=f j then 1 else 0) := by
    let t := s.erase j
    change _=(t.filter fun k => f k=i).card + _
    have hx : s=insert j t := (insert_erase hj).symm
    nth_rewrite 1 [hx]; rw [filter_insert]; by_cases hi : f j=i
    · rw [if_pos hi, card_insert_of_notMem, if_pos hi.symm]; exact fun H => notMem_erase _ _ (mem_filter.mp H).1
    rw [if_neg hi, if_neg (Ne.symm hi), add_zero]
  unfold deg; rw [leaves]; change _=( ((s.erase j).filter _).card + _) + _ + _
  rw [he,hb]
  change _ + (if i∈s then 1 else 0) = ( ((s.erase j).filter _).card + (if i∈s.erase j then 1 else 0) ) + _ + _
  by_cases hi : i=j
  · subst j; rw [if_pos hj,if_pos rfl,if_neg (notMem_erase _ _)]; omega
  have hx : i∈s.erase j ↔ i∈s := by simp [hi]
  simp only [hx,if_neg hi]; omega

variable [Fintype V]
/-- Enumerate true fusions. -/
def options (T A : Finset V) := @Finset.filter _ (Good T A) (fun _ => Classical.propDecidable _) univ
lemma choices (T A : Finset V) (f : Parent V) : f ∈ options T A ↔ Good T A f := by rw [options]; simp

lemma options_self (T : Finset V) : options T T={id} := by
  ext i; rw [choices,mem_singleton]; constructor
  · intro hi; exact funext fun x => hi.out x (by simp)
  intro hi; rw [hi]; refine ⟨by simp,by simp,?_⟩; simp

-- interchange sum. Sum over f' for each i,j equals sum over final
-- trees weighting each current eligible child j once. Needed ONLY for
-- actual contributions; for bounds use integrated mass per tree.
lemma choices_at (ha : A⊆T) (hi : i∈A) (hj : j∈T\A) :
    ((options T (insert j A)).image (fun f => join f j i))=
      ((options T A).filter fun f => f j=i) := by
  ext f; rw [mem_image,mem_filter]; constructor
  · rintro ⟨g,hg,rfl⟩; have hh := ((choices ..).mp hg).join_at ha hj hi
    exact ⟨(choices ..).mpr hh,update_self ..⟩
  rintro ⟨hg,hx⟩; refine ⟨cut f j,(choices ..).mpr (((choices ..).mp hg).cut_at hj),?_⟩
  rw [← hx]; exact join_cut ..

theorem swap_orders (ha : A⊆T) {W : Type} [AddCommMonoid W] (v : V → V → Parent V → W) :
    ∑ j∈(T \ A), ∑ i∈A, ∑ f∈options T (insert j A), v j i f =
      ∑ f∈options T A, ∑ j∈buds T A f,v j (f j) (cut f j) := by
  have he j (hj : j∈T\A) i (hi : i∈A) : ∑ f∈options T (insert j A),v j i f =
      ∑ f∈options T A, (if f j=i then v j (f j) (cut f j) else 0) := by
    let S := options T (insert j A)
    let g := fun f : Parent V => join f j i
    have hr (f : Parent V) (h : f∈S) := ((choices ..).1 h).cut_join i
    have hh : Set.InjOn g S := fun f hf l hl e => by rw [← hr f hf,← hr l hl]; exact congrArg (fun t => cut t j) e
    rw [← sum_filter,← choices_at ha hi hj,sum_image hh]
    apply sum_congr rfl; intro f hf
    change v j i f=v j ((join f j i) j) (cut (join f j i) j)
    rw [hr f hf]
    simp only [join, update_self]
  calc
    _ = ∑ j∈(T \ A),∑ i∈A,∑ f∈options T A,(if f j=i then v j (f j) (cut f j) else 0) :=
          sum_congr rfl fun j hj => sum_congr rfl fun i hi => he j hj i hi
    _ = _ := by
      have hi j : ∑ i∈A,∑ f∈options T A,(if f j=i then v j (f j) (cut f j) else 0)=∑ f∈options T A,
          (if f j ∈ A then v j (f j) (cut f j) else 0) := by rw [sum_comm]; simp
      simp_rw [hi]; rw [sum_comm]; simp [buds,sum_filter]
end Grove
end YM.Primitives.GCC
