import YM.OPE.Nesting.Parcels

/-! Complete signed moment comparisons with a child chosen before the
remaining symbols are combined. Term weights multiply in the full (not
connected) hierarchy. Only separated words ever participate. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
section
variable {I:Type} (j:I) (P:I→Type)
def dissect {I:Type} (j:I) (P:I→Type): (Σ i,P i) ≃ P j ⊕ (Σ i:{i:I//i≠j}, P i.val) where
   toFun t := if h:t.fst=j then Sum.inl (h ▸ t.snd) else Sum.inr ⟨⟨t.fst,h⟩,t.snd⟩
   invFun w:= Sum.elim (fun v=> ⟨j,v⟩) (fun t:Σ i:{i:I//i≠j},P i.val=> ⟨t.1.val,t.2⟩) w
   left_inv := by
     rintro ⟨i,t⟩; dsimp only
     by_cases h:i=j
     · subst i; rw [dif_pos rfl]; rfl
     rw [dif_neg h]; rfl
   right_inv := by
     rintro (a|⟨⟨i,h⟩,t⟩)
     · dsimp only [Sum.elim_inl]; rw [dif_pos rfl]
     dsimp only [Sum.elim_inr]; rw [dif_neg h]
lemma dissect_at (p:P j): dissect j P ⟨j,p⟩=Sum.inl p:=dif_pos rfl
lemma dissect_off {i:I}(p:P i)(h:i≠j):dissect j P ⟨i,p⟩=Sum.inr ⟨⟨i,h⟩,p⟩ :=dif_neg h

def bifurc (J:Type) := ((Equiv.sumCongr (dissect j P) (Equiv.refl J))).trans (Equiv.sumAssoc _ _ _)
lemma bifurc_main {J:Type}(p:P j) : bifurc j P J (Sum.inl ⟨j,p⟩)= Sum.inl p :=by unfold bifurc; erw [Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl,dissect_at]; rfl
lemma bifurc_rest {J:Type}{i:I}(p:P i) (hi:i≠j) : bifurc j P J (Sum.inl ⟨i,p⟩)=Sum.inr (Sum.inl ⟨⟨i,hi⟩,p⟩):=by unfold bifurc; erw [Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl,dissect_off j P p hi]; rfl
lemma bifurc_end {J:Type} (v:J) : bifurc j P J (Sum.inr v)=Sum.inr (Sum.inr v):=rfl
end

namespace Atom
variable {G:Gauge}{L':Register G}{S:Table L'}{K L I J:Type}[Fintype I][Fintype J]

def utter (v:I→S.Tag)(i:I):L'.Token:=names (voices v) i
lemma duet_reorder {K Q:Type}[Fintype K][Fintype Q] {T:Table L'}(ht:T.Hierarchy)(e:I⊕J ≃ K⊕Q)(x:I→E4)(y:J→E4)(x':K→E4)(y':Q→E4)(v:I→S.Tag)(w:J→S.Tag)(v':K→S.Tag)(w':Q→S.Tag)
    (hi:Injective (beside x y))(hx:∀ i:I⊕J,beside x y i=beside x' y' (e i))(hv:∀ i:I⊕J,beside v w i=beside v' w' (e i)) : duet T x v y w = duet T x' v' y' w':=by
       let m:=beside (utter v) (utter w); let n:=beside (utter v') (utter w')
       have hw:m=n ∘ ⇑e:=funext fun ij=>by
         let g(c:S.Tag):L'.Token:=⟨c.1,S.representative _ c.2⟩
         have hm:m ij=g (beside v w ij):=by cases ij <;> rfl
         have hn(ij'):n ij'=g (beside v' w' ij'):=by cases ij' <;> rfl
         exact hm.trans ((congr_arg g (hv ij)).trans (hn _).symm)
       have hx:beside x y=beside x' y' ∘ e:=funext hx
       have he:Injective (beside x' y'):= fun i j hij=>by
          obtain ⟨i,rfl⟩:= e.surjective i; obtain ⟨j,rfl⟩:= e.surjective j
          rw [hx] at hi
          exact congr_arg e (hi hij)
       rw [duet,duet,whole_observed,whole_observed]
       change observe T (beside x y) m=observe T _ n
       rw [hw,hx]; exact perm_observe T ht.laws.toSymmetric e n he

abbrev RestIndex (j:I):= {i:I//i≠j}
lemma explode_values (h : I→Atom S L)(j:I)
    {V:Type}(f:(Atom.bundle h).Slot→V) (f': ((h j).Slot⊕ (Atom.bundle fun k:RestIndex j=>h k.val).Slot) → V)
    (hf₁:∀ u, f ⟨j,u⟩=f' (.inl u))
    (hf₂:∀ (i:RestIndex j) u, f ⟨i.val,u⟩ = f' (.inr ⟨i,u⟩)) :∀ iv, f iv= f' ((dissect j (fun i=>(h i).Slot)) iv):=by
       rintro ⟨i,v⟩
       by_cases hv:i=j
       · subst i; rw [dissect_at]; exact hf₁ v
       rw [dissect_off _ _ _ hv]; exact hf₂ ⟨i,hv⟩ v

lemma explode (h:I→Atom S L)(T:Table L')(j:I)(y:J→E4)(w:J→S.Tag)(s:L) (hT:T.Hierarchy)(hv:Injective (beside ((Atom.bundle h).place s) y)):let h':=Atom.bundle fun k:RestIndex j=>h k.val
   duet T ((Atom.bundle h).place s) (Atom.bundle h).tags y w = duet T ((h j).place s) (h j).tags (beside (h'.place s) y) (splice h'.tags w):=by
      intros h'; let g:= bifurc j (fun i=>(h i).Slot) J
      refine duet_reorder hT g _ _ _ _ _ _ _ _ hv ?_ ?_
      · rintro (⟨i,p⟩|k)
        swap; · rfl
        change (h i).place s p=_
        by_cases hh:i=j; subst i
        · erw [bifurc_main j (fun i=>(h i).Slot)]; rfl
        erw [bifurc_rest j (fun i=>(h i).Slot) p hh]; rfl
      rintro (⟨i,p⟩|k)
      swap; · rfl
      change (h i).tags p=_
      by_cases hh:i=j; subst i
      · erw [bifurc_main j (fun i=>(h i).Slot)]; rfl
      erw [bifurc_rest j (fun i=>(h i).Slot) p hh]; rfl

lemma amp_alone (x:I→ℂ)(j:I):∏ i,x i= (∏ k:RestIndex j,x k.val)*x j:=by
      letI : Unique ({i:I // i=j}) := { default:=⟨j,rfl⟩, uniq:=fun a=>Subtype.ext a.prop }
      apply Eq.trans (Fintype.prod_subtype_mul_prod_subtype (fun i=>i=j) x).symm
      rw [mul_comm]; apply congr_arg; rw [@Fintype.prod_unique _ _ (Subtype.fintype _)]; rfl
lemma expose (h:I→Atom S L)(T:L→Table L')(j:I)(y:L→J→E4)(w:J→S.Tag)(s:L)(ht:(T s).Hierarchy)(hv:Injective (beside ((Atom.bundle h).place s) (y s))) :
   let h':=Atom.bundle fun k:RestIndex j=>h k.val
   (Atom.bundle h).sample T y w s = h'.amp s * (h j).sample T (fun s=> beside (h'.place s) (y s)) (splice h'.tags w) s:=by
      intros h'; unfold sample; change (∏ i,(h i).amp s)*duet ..= _; rw [amp_alone _ j,explode h (T s) j (y s) w s ht hv]; exact mul_assoc _ _ _
end Atom

namespace Menu
open Atom
variable {G:Gauge}{L':Register G}{S:Table L'}{K L I J:Type}[Fintype I][Fintype J]

def rest (P:I→Menu S L)(j:I):Menu S L :=fuse (fun i:RestIndex j=>P i.val)
lemma rest_eq {P P':I→Menu S L}(j:I)(h:∀i≠j,P i=P' i):rest P j=rest P' j:= congr_arg fuse (funext fun (a:RestIndex j)=> h a a.prop)

def attached (P:I→Menu S L)(j:I)(y:L→J→E4)(w:J→S.Tag)(T:L→Table L')(s:L)(q:(rest P j).Draw) :=
    let z:=(rest P j).pick q
    z.amp s*(P j).atView T (fun s=> beside (z.place s) (y s)) (splice z.tags w) s

def taxi (Z:Atom S L)(T:L→Table L')(P:Menu S L)(y:L→J→E4)(w:J→S.Tag)(s:L):ℂ := (P.atView T (fun s=>beside (Z.place s) (y s)) (splice Z.tags w) s) * Z.amp s

lemma disrupt (P:I→Menu S L)(T:L→Table L')(j:I)(y:L→J→E4)(w:J→S.Tag)(s:L)(ht:(T s).Hierarchy)
      (hv: ∀ k:(fuse P).Draw,Injective (beside (((fuse P).pick k).place s) (y s))):
      (fuse P).atView T y w s= ∑ k:(rest P j).Draw,(attached P j y w T s k):=by
         unfold atView; let Lf:= fun (p:(fuse P).Draw)=> ((fuse P).pick p).sample T y w s
         let Rf:= fun (k:(P j).Draw × (rest P j).Draw)=> let z:=(rest P j).pick k.2; z.amp s*((P j).pick k.1).sample T (fun s=> beside (z.place s) (y s)) (splice z.tags w) s
         change (∑ c:(fuse P).Draw,Lf c) = _
         let e:(fuse P).Draw ≃ (P j).Draw × (rest P j).Draw := Equiv.piSplitAt j (fun i=>(P i).Draw)
         rw [Fintype.sum_equiv e Lf Rf (fun x=>?_)]
         · rw [Fintype.sum_prod_type,Finset.sum_comm]; refine Finset.sum_congr rfl fun k hk=>?_ 
           unfold attached atView; rw [Finset.mul_sum]
         change (Atom.bundle (fun i=>(P i).pick (x i))).sample T y w s=_; change _ = Rf (e x); unfold Rf e; simp only [Equiv.piSplitAt_apply]; exact expose _ T j y w s ht (hv x)

lemma taxi_formula (P:I→Menu S L)(T:L→Table L')(j:I)(y:L→J→E4)(w:J→S.Tag)(s:L)(ht:(T s).Hierarchy)
      (hv: ∀ k:(fuse P).Draw,Injective (beside (((fuse P).pick k).place s) (y s))) (Z:Menu S L)(he:rest P j=Z):
      (fuse P).atView T y w s= ∑ k:Z.Draw, taxi (Z.pick k) T (P j) y w s:=by
        subst Z; rw [disrupt P T j y w s ht hv]; apply Finset.sum_congr rfl fun _ _=>mul_comm ..
end Menu
end YM.OPE.Nesting
