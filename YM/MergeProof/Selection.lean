import YM.MergeProof.Switch
/-! # Choosing distinct occupied wings. -/
set_option autoImplicit false
noncomputable section
namespace YM.Merge
open Function Finset
open scoped BigOperators Classical
variable {ι β χ α : Type} [Fintype ι][DecidableEq β]
    (w : ι→β)

def Draft (t:Finset ι): Prop := Set.InjOn w (t:Set ι)
abbrev Tickets:= {t: Finset ι // Draft w t}
namespace Tickets
variable {w}
def reach (v:Tickets w): Finset β:= v.val.image w
omit [Fintype ι] in
@[simp] lemma reaches_of {i} (v:Tickets w)(hi:i∈v.val): w i∈ v.reach:=mem_image_of_mem _ hi

def none (w:ι→β): Tickets w:=⟨∅,by simp [Draft]⟩
omit [Fintype ι] in
lemma empty (p:Tickets w)(h:p.reach⊆ ∅): p=none w:= Subtype.ext (Finset.eq_empty_iff_forall_notMem.mpr fun _i hi=> Finset.notMem_empty _ (h (p.reaches_of hi)))

def select (p:Tickets w)(U:Finset β): Tickets w:= ⟨p.val.filter fun i=>w i∈U,p.property.mono (filter_subset ..)⟩
omit [Fintype ι] in
lemma selected (p:Tickets w)(U:Finset β): (select p U).reach ⊆ U:=by
  intro i hi; obtain ⟨j,h,rfl⟩:=mem_image.mp hi; exact (mem_filter.mp h).2

omit [Fintype ι] in
private lemma selection (p : Tickets w) (A U : Finset β) (r : ι→α) [CommMonoid α] (h:Disjoint A U)(hp:p.reach⊆ A∪U): (∏ i∈p.val, r i)=(∏ i∈(select p A).val,r i)*∏ j∈(select p U).val,r j:=by
  let a:=select p A; let b:=select p U; have hh:p.val=a.val∪b.val:=by
    ext i; constructor
    · intro h; rcases mem_union.mp (hp (p.reaches_of h)) with hx|hx; exact mem_union_left _ (mem_filter.mpr ⟨h,hx⟩); exact mem_union_right _ (mem_filter.mpr ⟨h,hx⟩)
    intro h; rcases mem_union.mp h with hx|hx <;> exact (mem_filter.mp hx).1
  nth_rw 1 [hh]; exact prod_union (Finset.disjoint_left.mpr fun i hi hk=> Finset.disjoint_left.mp h ((mem_filter.mp hi).2) ((mem_filter.mp hk).2))

variable {A B : Finset β}(p q : Tickets w)
omit [Fintype ι] in
def graft (h:Disjoint A B)(hp:p.reach⊆A) (hq:q.reach⊆ B): Tickets w:=⟨p.val∪q.val,fun i hi j hj hz=>by
  rcases mem_union.mp hi with hi|hi <;> rcases mem_union.mp hj with hj|hj
  · exact p.prop hi hj hz
  · exact False.elim (Finset.disjoint_left.mp h (hp (p.reaches_of hi)) (hz.symm ▸ hq (q.reaches_of hj)))
  · exact False.elim (Finset.disjoint_left.mp h (hp (p.reaches_of hj)) (hz ▸ hq (q.reaches_of hi)))
  exact q.prop hi hj hz⟩

abbrev Applies (w:ι→β)(A:Finset β):= {p : Tickets w // p.reach ⊆ A}
omit [Fintype ι] in
def sever (h:Disjoint A B) (w:ι→β): Applies w (A∪B) ≃ Applies w A × Applies w B where
  toFun p:= (⟨p.val.select A,selected ..⟩,⟨p.val.select B,selected ..⟩)
  invFun x:= ⟨graft x.1.val x.2.val h x.1.prop x.2.prop,by
    unfold reach graft; rw [Finset.image_union]; exact union_subset_union x.1.property x.2.property⟩
  left_inv p:= by
    apply Subtype.ext; apply Subtype.ext; ext i; constructor
    · intro h; rcases mem_union.mp h with hx|hx<;> exact (mem_filter.mp hx).1
    intro hi; rcases mem_union.mp (p.prop (p.val.reaches_of hi)) with hx|hx; exact mem_union_left _ (mem_filter.mpr ⟨hi,hx⟩); exact mem_union_right _ (mem_filter.mpr ⟨hi,hx⟩)
  right_inv x:=by
    apply Prod.ext
    · apply Subtype.ext; apply Subtype.ext; ext i; constructor
      · intro hk; obtain ⟨hk,hp⟩:= mem_filter.mp hk; rcases mem_union.mp hk with hk|hk; exact hk; exact False.elim (Finset.disjoint_left.mp h hp (x.2.prop (x.2.val.reaches_of hk)))
      intro hi; exact mem_filter.mpr ⟨mem_union_left _ hi,x.1.prop (x.1.val.reaches_of hi)⟩
    apply Subtype.ext; apply Subtype.ext; ext i; constructor
    · intro hk; obtain ⟨hk,hp⟩:= mem_filter.mp hk; rcases mem_union.mp hk with hk|hk; exact False.elim (Finset.disjoint_left.mp h (x.1.prop (x.1.val.reaches_of hk)) hp); exact hk
    intro hi; exact mem_filter.mpr ⟨mem_union_right _ hi,x.2.prop (x.2.val.reaches_of hi)⟩

-- classical issue macros. test variable χ polygon.
section
variable [CommSemiring α]
lemma on_record (S : Finset χ)(P : χ→ Finset β) (h : (S:Set χ).PairwiseDisjoint P) (f : χ → Tickets w→α) (z : ι→α):
    (∏ i∈S,∑ j : Applies w (P i),(∏ i∈j.val.val,z i)* f i j.val) =
      ∑ j : Applies w (S.biUnion P),(∏ i ∈ j.val.val,z i)*∏ i∈S, f i (j.val.select (P i)):=by
   induction S using Finset.induction with
   | empty =>
      let A:=Applies w ((∅:Finset χ).biUnion P); let b:A:= ⟨none w,by simp [reach,none]⟩
      symm; rw [Finset.sum_eq_single b]; · simp [b,none]
      · exact fun j hj h=> False.elim (h (Subtype.ext (j.val.empty (by have h:= j.prop; simpa using h))))
      exact fun h=>False.elim (h (Finset.mem_univ b))
   | insert i S hi ih=>
      let T:=insert i S; let A:=P i; let B:=S.biUnion P
      have hp: (S:Set χ).PairwiseDisjoint P:=fun _ hx _ hy=> h (mem_insert_of_mem hx) (mem_insert_of_mem hy)
      have he : Disjoint A B:=Finset.disjoint_left.mpr fun j hj hx=> by obtain ⟨k,hk,hX⟩:= mem_biUnion.mp hx; exact Finset.disjoint_left.mp (h (mem_insert_self ..) (mem_insert_of_mem hk) (fun hx=>hi (hx.symm ▸ hk))) hj hX
      rw [prod_insert hi, ih hp]; rw [Finset.biUnion_insert]
      let X (t:Applies w A):=(∏ j∈t.val.val,z j)*f i t.val
      let Y (t:Applies w B):=(∏ j∈t.val.val,z j)*∏ i∈ S,f i (t.val.select (P i))
      change (∑ t,X t)*(∑ t,Y t)= ∑ j : Applies w (A∪B), _
      rw [sum_mul]; simp_rw [Finset.mul_sum]; rw [← Fintype.sum_prod_type (fun p : Applies w A × Applies w B=>X p.1 *Y p.2)]; symm; refine Fintype.sum_equiv (sever he w) _ _ ?_
      intro p; change _ = X ⟨p.val.select A,_⟩ * Y ⟨p.val.select B,_⟩; unfold X Y
      have hz(k:χ)(hk:k∈S) : select p.val (P k)= (p.val.select B).select (P k):= by
        apply Subtype.ext; ext j; constructor
        · intro h; obtain ⟨h,u⟩:=mem_filter.mp h; exact mem_filter.mpr ⟨mem_filter.mpr ⟨h,mem_biUnion.mpr ⟨_,hk,u⟩⟩,u⟩
        intro h; obtain ⟨h,u⟩:=mem_filter.mp h; exact mem_filter.mpr ⟨(mem_filter.mp h).1,u⟩
      simp_rw [selection p.val A B z he p.prop,prod_insert hi]; rw [prod_congr rfl (fun j (hj:j∈S)=> congr_arg (f j) (hz j hj))]; ac_rfl
lemma confined (f:Tickets w→α)(z: Finset β) (hp:∀ p,f p ≠ 0→p.reach⊆z): (∑p,f p)=∑ p : Applies w z,f p.val :=by
   symm; apply Finset.sum_of_injOn Subtype.val (fun _ _ _ _=>Subtype.ext) (fun _ _=>Finset.mem_univ _) ?_ (fun _ _=> rfl)
   intro i _ hi; by_contra h; apply hi; exact ⟨⟨i,hp i h⟩, mem_univ _,rfl⟩
end
end Tickets
end YM.Merge
