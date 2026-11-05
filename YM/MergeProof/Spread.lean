import YM.MergeProof.Selection
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Tickets
open Function Finset
open scoped BigOperators Classical
variable {ι β α : Type} [Fintype ι][DecidableEq β][CommSemiring α](w:ι→β)(u v : ι)
def mono (w:ι→β)(u : ι): Tickets w:= ⟨{u},by simp [Draft]⟩
variable (v: β→α)(f:ι→α)
omit [Fintype ι] in
lemma singleton_budget (i:β) (p:Tickets w)(hp : p.reach⊆{i}) : p=none w ∨ ∃ j, w j=i ∧ p=mono w j:=by
  by_cases hz:p.val=∅; exact Or.inl (Subtype.ext hz)
  obtain ⟨k,hk⟩:=nonempty_iff_ne_empty.mpr hz
  have ht (j)(hj:j∈p.val):w j=i:= mem_singleton.mp (hp (p.reaches_of hj))
  refine Or.inr ⟨k,ht k hk,Subtype.ext (Finset.eq_singleton_iff_unique_mem.mpr ⟨hk,fun j hj=> p.prop hj hk ((ht _ hj).trans (ht _ hk).symm)⟩)⟩

def extra (i:β): α:=∑ j, if w j=i then f j else 0
lemma summand (i:β) : ∑ j:Applies w {i},(∏ k∈j.val.val, f k)* (if i∈ j.val.reach then 1 else v i)=v i+extra w f i:=by
  let a:Applies w {i}:=⟨none w,by simp [reach,none]⟩
  let s:= fun p: Applies w {i}=> (∏ k∈p.val.val, f k)*(if i∈ p.val.reach then 1 else v i)
  change (∑ i,s i)=_
  rw [← add_sum_erase _ _ (mem_univ a),show s a=v i from by simp [s,a,none,reach],extra,← Finset.sum_filter]
  apply congr_arg; symm
  let g (j:ι) (h:j∈univ.filter (fun k=>w k=i)): Applies w {i}:=⟨mono w j,(by simp [reach,mono,(mem_filter.mp h).2])⟩
  refine Finset.sum_bij g ?_ ?_ ?_ ?_
  · intro k hk; exact mem_erase.mpr ⟨fun h=> (singleton_ne_empty _) (congr_arg (fun i:Applies w {i}=>i.val.val) h),mem_univ _⟩
  · intro x hx y hy h; exact Finset.singleton_inj.mp (congr_arg (fun i:Applies w {i}=>i.val.val) h)
  · intro b hb; rcases singleton_budget w i b.val b.prop with hf|⟨k,h,h'⟩ -- α? implicit omitted
    · exact False.elim (ne_of_mem_erase hb (Subtype.ext hf))
    exact ⟨k,mem_filter.mpr ⟨mem_univ _,h⟩,Subtype.ext h'.symm⟩
  intro k hk; simp [s,g,mono,reach, (mem_filter.mp hk).2]

lemma expanded (b:Finset β): ∏ i∈b,(v i+extra w f i)=∑ j:Tickets w, if j.reach⊆ b then (∏ i∈j.val,f i)*∏ i∈b\j.reach,v i else 0:=by
  let P (i:β): Finset β:={i}
  let g i (p: Tickets w):= if i∈p.reach then 1 else v i
  have ht : (b:Set β).PairwiseDisjoint P:=fun i _ j _ he=>Finset.disjoint_singleton.mpr he
  simp_rw [← summand]; rw [on_record (w:=w) b P ht g]
  let p (i: Tickets w):= if i.reach ⊆ b then (∏ j∈i.val,f j)*∏j∈b\i.reach,v j else 0
  change _=∑ j,p j
  have he := confined p (b.biUnion P) (fun q h=> (show b.biUnion P=b by simp [P]) |>.symm ▸ (show q.reach⊆ b from Classical.byContradiction fun hx=> h (if_neg hx)))
  rw [he]; refine sum_congr rfl fun i hi=>?_
  have hB : i.val.reach⊆b:=by have h:=i.prop; simpa [P] using h
  unfold p; rw [if_pos hB]; apply congr_arg
  have hp (j:β): g j (select i.val (P j))= if j∈ i.val.reach then 1 else v j:= by
    unfold g; congr 1; ext -- edit
    unfold select reach P; simp only [mem_image,mem_filter,mem_singleton]; grind
  let f'(j:β):=if j∈i.val.reach then (1:α) else v j
  rw [prod_congr rfl (fun j (_:j∈b) => hp j)]; change (∏ j∈b,f' j)=_
  rw [← prod_subset (s₂:=b) (s₁:=b\i.val.reach) (f:=f') (sdiff_subset) ?_];exact prod_congr rfl fun j hj=>if_neg (Finset.mem_sdiff.mp hj).2
  exact fun j hj ht=>if_pos (by by_contra hn; exact ht (mem_sdiff.mpr ⟨hj,hn⟩))
end YM.Merge.Tickets
