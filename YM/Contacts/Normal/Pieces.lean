import YM.Contacts.Normal.Dimension
import YM.Contacts.Score.Order

/-! # Refinements of disjoint strict patches -/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Set Finset MeasureTheory Ordered
open scoped Topology BigOperators Classical
variable {k : ℕ} {g p l : Group k}
abbrev Pieces (u : Group k) := Finpartition u
variable {P Q : Pieces g}

lemma one_set (P : Pieces g) (hp : P=⊤) (hg : g.Nonempty) : P.parts={g}:= by
  subst P; have hu:= Finpartition.parts_top_subset g; obtain ⟨x,hx⟩:= Finpartition.parts_nonempty (⊤:Pieces g) hg.ne_empty; have he:= mem_singleton.mp (hu hx); exact Subset.antisymm hu (singleton_subset_iff.mpr (he ▸ hx)) -- Finset namespace
lemma contains_self_is_top (h : g ∈ P.parts) : P=⊤ := by
  apply top_unique; intro p hp; rw [one_set _ rfl (P.nonempty_of_mem_parts h)] at hp; exact ⟨_,h,(mem_singleton.mp hp).le⟩
lemma inner_piece (P : Pieces g) (hP : P≠⊤) {f:Group k} (hf:f∈P.parts) : f ⊂ g:= Finset.ssubset_iff_subset_ne.mpr ⟨P.subset hf, fun he=> hP (contains_self_is_top (he ▸ hf))⟩
lemma many (hP : P≠⊤) (hg:g.Nonempty): ∃ i∈P.parts, ∃ j∈P.parts,i≠j:=by
  obtain ⟨i,hi⟩:= P.parts_nonempty hg.ne_empty; obtain ⟨x,hx,hh⟩:= Finset.exists_of_ssubset (inner_piece P hP hi); obtain ⟨j,hj,hj'⟩:= P.exists_mem hx -- order check
  exact ⟨i,hi,j,hj,fun h=> hh (h ▸ hj')⟩
lemma many_card (hP : P≠⊤) (hg : g.Nonempty) : 1 < P.parts.card := Finset.one_lt_card.mpr (many hP hg)
lemma top_of_single (i : Fin k) (P : Pieces {i}): P=⊤:=by by_contra h; have he:=(many_card h (singleton_nonempty i)).trans_le P.card_parts_le_card; simp at he

/-- child subpartitions. -/
abbrev choices (P : Pieces g) := (a:P.parts) → Pieces a.val
def stitch (P : Pieces g) (C : choices P) := P.bind fun a ha=> C ⟨a,ha⟩
lemma stitches {C : choices P}: p∈ (stitch P C).parts ↔ ∃ a:P.parts, p∈ (C a).parts:= by simp only [stitch,Finpartition.mem_bind,Subtype.exists]
lemma stitch_le {C : choices P}: stitch P C ≤ P:= fun x hx=> by obtain ⟨a,ha⟩:=(stitches.mp hx); exact ⟨_,a.property,(C a).le ha⟩
lemma parent_uniq (e f : P.parts) (h : p.Nonempty) (he : p ⊆ e.val) (hf : p ⊆ f.val) : e=f:= by
    obtain ⟨x,hx⟩:=h; exact Subtype.ext (P.eq_of_mem_parts e.property f.property (he hx) (hf hx))
lemma stitch_loc {C : choices P} (v : P.parts) :
     p∈(C v).parts ↔ p ∈ (stitch P C).parts ∧ p ⊆ v.val := by
  refine ⟨fun h=> ⟨stitches.mpr ⟨v,h⟩,(C v).subset h⟩,fun ⟨h,h'⟩=>?_⟩
  obtain ⟨a,h⟩:= stitches.mp h; obtain rfl : v=a:= parent_uniq _ _ ((C a).nonempty_of_mem_parts h) h' ((C a).subset h); exact h

def portion (h : P ≤ Q) : choices Q:= fun a=> P.ofSubset (parts:=P.parts.filter (fun y=> y ⊆ a.val)) (filter_subset _ _) (by
  ext i; rw [mem_sup]; constructor
  · rintro ⟨b,hb,h⟩; exact (mem_filter.mp hb).2 h
  intro hi; obtain ⟨b,hb,hB⟩:= P.exists_mem (Q.subset a.property hi); obtain ⟨q,hq,hU⟩:= h hb
  have he:q=a.val:= Q.eq_of_mem_parts hq a.property (hU hB) hi; exact ⟨b,mem_filter.mpr ⟨hb,by subst q; exact hU⟩,hB⟩)
lemma stitch_bijection (P : Pieces g) : Bijective (fun C : choices P=> (⟨stitch P C,stitch_le⟩ : Set.Iic P)) := by
  constructor
  · intro C D h; have he:stitch P C=stitch P D:= Subtype.ext_iff.mp h; funext a; ext t; rw [stitch_loc a,stitch_loc a,he]
  rintro ⟨Q,hQ⟩; refine ⟨portion hQ,Subtype.ext (?_)⟩; change stitch _ _ = Q
  ext x; rw [stitches]; constructor
  · rintro ⟨a,ha⟩; exact (mem_filter.mp ha).1
  intro hx; obtain ⟨y,hy,hc⟩:= (hQ : Q ≤ P) hx; exact ⟨⟨y,hy⟩,mem_filter.mpr ⟨hx,hc⟩⟩
lemma crossing (h : ¬ P ≤ Q) : ∃ p∈P.parts, ∃ A∈Q.parts,∃ B∈Q.parts, B ≠ A ∧
    ∃ i∈ p,∃ j∈ p,i∈ A∧j∈B := by
  have hh : ¬ (∀ a∈ P.parts, ∃ b∈ Q.parts,a ≤ b):= fun hg=>h (fun x hx=>hg _ hx)
  push Not at hh; obtain ⟨p,hp,hg⟩:= hh; obtain ⟨i,hi⟩:=P.nonempty_of_mem_parts hp; obtain ⟨A,hA,hi'⟩:= Q.exists_mem (P.le hp hi)
  obtain ⟨j,hj,hj'⟩:= Finset.not_subset.mp (hg A hA); obtain ⟨B,hB,hh⟩:= Q.exists_mem (P.le hp hj); exact ⟨p,hp,A,hA,B,hB,fun h=> hj' (h ▸ hh), i,hi,j,hj,hi',hh⟩

/-- union from splitting one open block. -/
def replace (v : P.parts) (Q : Pieces v.val) : Pieces g:= stitch P (Function.update (fun _=>⊤) v Q)
lemma replace_parts (i : P.parts) (Q : Pieces i.val) : (replace i Q).parts = P.parts.erase i.val ∪ Q.parts := by
   ext x; rw [replace,stitches,Finset.mem_union]; constructor
   · rintro ⟨j,hj⟩; by_cases h:j=i
     · subst j; right; rw [Function.update_self] at hj; exact hj
     rw [Function.update_of_ne h] at hj; have hh:x=j.val:= mem_singleton.mp (by rw [← one_set (⊤:Pieces j.val) rfl (P.nonempty_of_mem_parts j.property)]; exact hj); subst x; exact Or.inl (mem_erase.mpr ⟨Subtype.val_injective.ne h,j.property⟩)
   rintro (h|h)
   · obtain ⟨hh,h⟩:= mem_erase.mp h; let j:P.parts:=⟨x,h⟩; refine ⟨j,?_⟩; rw [Function.update_of_ne (show j≠i from fun h=>hh (congr_arg Subtype.val h)),one_set _ rfl (P.nonempty_of_mem_parts j.property)]; exact mem_singleton_self _
   exact ⟨i,by simp only [Function.update_self,h]⟩
lemma replace_disj (i : P.parts) (Q : Pieces i.val) : Disjoint (P.parts.erase i.val) Q.parts := by
   refine Finset.disjoint_left.mpr (fun x hx hc=>?_); obtain ⟨hh,he⟩:= mem_erase.mp hx
   obtain ⟨z,hz⟩:= P.nonempty_of_mem_parts he; exact hh (P.eq_of_mem_parts he i.property hz (Q.le hc hz))
lemma replace_finer (i : P.parts) {Q : Pieces i.val}(h : Q≠⊤) : P.parts.card < (replace i Q).parts.card:= by
   rw [replace_parts, card_union_of_disjoint (replace_disj ..),← Finset.card_erase_add_one i.property]; exact Nat.add_lt_add_left (many_card h (P.nonempty_of_mem_parts i.property)) _ -- order LHS converted? 
lemma costs_bind {β : Type*} [AddCommMonoid β] (P:Pieces g) (d: Fin k→β) : g.sum d=P.parts.sum (fun b=>b.sum d):=by
   conv_lhs => rw [← P.biUnion_parts]
   exact Finset.sum_biUnion P.disjoint
end YM.Contacts.Normal
