import YM.RG08.Gallery.Neon

/-!
# First slot separation from full sparse law
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Gallery
open Forms Glyph Room Camera Finset Lattice Laurent Pert.Bulk Function MvPolynomial Filter Isles
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {I:Type}{n:ℕ}
private def trim (S:Finset I)(a: ↥S→ℝ):Demo I:=⟨S,fun i=>if h:i∈S then a ⟨i,h⟩ else 0,fun _ hi=>dif_neg hi⟩
def handles (S:Finset I)(x:Tape n ↥S):Tape n I:= fun i=>(x i).val
private def march (S:Finset I)(n:ℕ):Tape n ↥S≃ ↥(desks S n):={
 toFun x:=⟨handles S x, Fintype.mem_piFinset.mpr (fun i=> (x i).property)⟩
 invFun x:=fun i=>⟨x.val i,Fintype.mem_piFinset.mp x.property i⟩
 left_inv _:=rfl
 right_inv _:=rfl}
lemma regard_poly (S:Finset I)(F:Flake n I)(a:Demo I)(hx:a.firm⊆S) :
    regard F a=MvPolynomial.eval (a.play ∘ ((↑):S→I)) (parley (F ∘ handles S)):=by
 rw [regard_price _ _ hx,parley,map_sum]
 let f(x:Tape n I):=F x*basic a x
 change (∑ x∈desks S n,f x)=_
 rw [← Finset.sum_coe_sort (desks S n), ←(march S n).sum_comp];apply Finset.sum_congr rfl;intro i _
 simp only [comp_apply,MvPolynomial.smul_eq_C_mul,map_mul,eval_C,word,map_prod,eval_X];rfl

lemma lift_demo(S:Finset I)(f:Tape n I)(h:∀ i,f i∈S): ∃ g:Tape n ↥S,f=handles S g:=⟨fun i=>⟨_,h i⟩,rfl⟩

lemma work_first {F:Flake (n+1) I}(h:Sym F)(b:Demo I)(he:∀ (a c:Demo I)(x:ℝ), c.play=a.play+x • b.play→ regard F a=regard F c)(y:Tape n I):
    (∑ j∈b.firm,b.play j * F (Fin.cons j y))=0:=by
 let S:= b.firm∪(univ.image y)
 obtain ⟨v,hv⟩:=lift_demo S y (fun i=> Finset.mem_union_right _ (Finset.mem_image_of_mem y (mem_univ _)))
 let g:=F ∘ handles (n:=n+1) S
 have hg:Sym g:=fun e=>funext fun i=>congrFun (h e) (handles S i)
 have ht:=first_gap hg (fun j=>b.play j.val) ?_ v
 swap
 · intro x a
   let A:=trim S a
   let C:=Demo.add A (Demo.reals x b)
   have ht:=he A C x rfl
   rw [regard_poly S _ _ (subset_refl _),regard_poly S _ _ (Finset.union_subset (subset_refl S) Finset.subset_union_left)] at ht
   convert ht.symm using 1
   · congr 2;funext j; simp [C,Demo.add,A,trim,Demo.reals]
   congr 2; funext j;simp [A,trim]
 have hh : (∑ j:S,b.play j.val * g (Fin.cons j v)) = ∑ j∈S,b.play j*F (Fin.cons j y):=by
    rw [←Finset.sum_coe_sort S];apply Finset.sum_congr rfl;intro j _;congr 1; unfold g;change F _=_;apply congrArg F; ext i;cases i using Fin.cases <;>simp [handles,hv]
 rwa [hh,←Finset.sum_subset (s₁:=b.firm) Finset.subset_union_left (fun j _ hj=>by rw [b.size' _ hj,zero_mul])] at ht

lemma work_any {F:Flake n I}(h:Sym F)(b:Demo I)(he:∀ (a c:Demo I)(x:ℝ),c.play=a.play+x • b.play→ regard F a=regard F c)(y:Tape n I)(i:Fin n): (∑ j∈b.firm,b.play j* F (update y i j))=0:=by
 rcases n with _|n; · exact Fin.elim0 i
 let e:= Equiv.swap 0 i
 let W:= Fin.tail (y ∘ ⇑e)
 convert work_first h b he W using 1
 apply Finset.sum_congr rfl;intro j _;congr 1
 apply Eq.trans ?_ (show F (Fin.cons j W ∘ ⇑e)=F _ from congrFun (h e) _)
 apply congrArg F;ext k
 by_cases hk:k=i
 · rw [hk,update_self]; dsimp [e];simp
 by_cases hz:k=0
 · subst k;rw [update_of_ne hk];change y 0=(Fin.cons j W :Tape (n+1) I) (e 0);rw [show e 0=i from Equiv.swap_apply_left 0 i]
   obtain ⟨l,hl⟩:= Fin.exists_succ_eq.mpr (Ne.symm hk)
   rw [←hl,Fin.cons_succ];change _= y (e l.succ);rw [hl];exact (congrArg y (Equiv.swap_apply_right 0 i)).symm
 rw [update_of_ne hk];change y k=(Fin.cons j W :Tape (n+1) I) (e k);rw [show e k=k from Equiv.swap_apply_of_ne_of_ne hz hk];obtain ⟨l,rfl⟩:=Fin.exists_succ_eq.mpr hz;rw [Fin.cons_succ];change _=y (e l.succ);rw [show e l.succ=l.succ from Equiv.swap_apply_of_ne_of_ne hz hk]
end YM.RG08.Gallery
