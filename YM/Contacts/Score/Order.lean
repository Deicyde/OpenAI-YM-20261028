import Mathlib.Data.Finset.NoncommProd
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Ordered products of Taylor instructions on disjoint slot sets

Use a fixed order to state identities. This algebra is *not* commutative (an inner Taylor
subtraction in a nested term cannot be moved arbitrarily). It suffices that assignments on
separated slot sets can move past one another.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Ordered
open Function Set
open scoped BigOperators Classical
variable {A B I J : Type*} [DecidableEq I]

section Ring
variable [Ring A]
def assembly (A: Type*) [Ring A] (s : Finset I) : MultilinearMap ℤ (fun _:s => A) A:=
 (MultilinearMap.mkPiAlgebraFin ℤ _ A).domDomCongr (Fintype.equivFin s).symm
/-- total product, meaningful without `[DecidableEq]`? retains canonical choice. -/
def product (s : Finset I) (p : I→ A) := assembly A s (fun i=>p i)
omit [DecidableEq I] in
lemma eq_product {s : Finset I}{p q : I→A} (h : ∀ i∈s,p i=q i) : product s p=product s q := congrArg (assembly A s) (funext fun i=>h _ i.property)
lemma actual (s : Finset I)(f : I→A) (h : (s:Set I).Pairwise (fun i j=> Commute (f i) (f j))) : product s f=s.noncommProd f h := by
   let e:= (Fintype.equivFin s).symm
   let p: Fin (Fintype.card s) → I:= fun i=>e i; have hp : Injective p:= Subtype.val_injective.comp e.injective
   let L:= List.ofFn p; have hL:L.toFinset=s:= by
     ext i; unfold L; simp only [List.mem_toFinset,List.mem_ofFn]; constructor; rintro ⟨i,rfl⟩; exact (e i).property
     intro h; exact ⟨e.symm ⟨i,h⟩, show (e _).val=i from congrArg (Subtype.val) (e.apply_symm_apply _)⟩
   trans L.toFinset.noncommProd f (show (L.toFinset:Set I).Pairwise _ by rw [hL]; exact h)
   · rw [Finset.noncommProd_toFinset L f _ (List.nodup_ofFn.mpr hp), show L.map f=List.ofFn (fun i=> f (p i)) from List.map_ofFn ..]; rfl
   congr
@[simp] lemma product_empty (f:I→A):product ∅ f=1:= by rw [actual (∅:Finset I) _ (by simp), Finset.noncommProd_empty]
@[simp] lemma product_one (i:I)(f:I→A):product {i} f=f i:= by rw [actual {i} _ (by simp),Finset.noncommProd_singleton]
lemma product_insert {s : Finset I} {i:I}(f:I→ A)(h : i∉s)(hh : (↑(insert i s):Set I).Pairwise (fun i j=>Commute (f i) (f j))) : product (insert i s) f=f i*product s f:= by rw [actual (insert i s) _ hh,actual s _ (hh.mono (Finset.coe_subset.mpr (Finset.subset_insert _ _))),Finset.noncommProd_insert_of_notMem _ _ _ _ h]
lemma split_head (s : Finset I) {i : I} (hi : i∈s)(p : I→A)(h : (s:Set I).Pairwise fun i j=>Commute (p i) (p j)) : product s p=p i*product (s.erase i) p := by rw [actual _ _ h,actual _ _ (h.mono (Finset.coe_subset.mpr (Finset.erase_subset ..)))]; exact (Finset.mul_noncommProd_erase s hi p h).symm
lemma split_last (s : Finset I) {i : I} (hi : i∈s)(p : I→A)(h : (s:Set I).Pairwise fun i j=>Commute (p i) (p j)) : product s p=product (s.erase i) p*p i := by rw [actual _ _ h,actual _ _ (h.mono (Finset.coe_subset.mpr (Finset.erase_subset ..)))]; exact (Finset.noncommProd_erase_mul s hi p h).symm
lemma moves (p : Finset I)(f:I→A)(a:A)(h:(p:Set I).Pairwise (fun i j=>Commute (f i) (f j)))(ha:∀ i∈p,Commute (f i) a): Commute (product p f) a:= by rw [actual p f h]; exact (Finset.noncommProd_commute p f h a (fun i hi=>(ha i hi).symm)).symm
lemma union_commutes {s t : Finset I}(h:Disjoint s t)(f:I→A)(hc: (↑(s∪t):Set I).Pairwise (fun i j=>Commute (f i) (f j))): product (s∪t) f= product s f* product t f:=by
  rw [actual (s∪t) f hc,actual s f (hc.mono (Finset.coe_subset.mpr Finset.subset_union_left)), actual t f (hc.mono (Finset.coe_subset.mpr Finset.subset_union_right))]; exact Finset.noncommProd_union_of_disjoint h f hc
variable [DecidableEq J]
lemma gather_product {s : Finset J} (t : J → Finset I) (f : I → A)
    (h : (s:Set J).Pairwise fun i j=> Disjoint (t i) (t j)) (hc : (↑(s.biUnion t):Set I).Pairwise fun i j=> Commute (f i) (f j)) :
    product (s.biUnion t) f= product s (fun j=> product (t j) f) := by
  induction s using Finset.induction_on with
  | empty=> simp
  | @insert j s hj ih=>
    let p:=insert j s; have ht(i : J)(hx : i∈p) : (t i : Set I)⊆ ↑(p.biUnion t):= by intro x h; exact Finset.mem_biUnion.mpr ⟨_,hx,h⟩
    have hh : (s:Set J)⊆ (p:Set J):=Finset.coe_subset.mpr (Finset.subset_insert _ _)
    have hq : (↑(s.biUnion t):Set I) ⊆ ↑(p.biUnion t):=by rintro i hi; obtain ⟨k,hk,h⟩:= Finset.mem_biUnion.mp hi; exact ht _ (hh hk) h
    have H : (p:Set J).Pairwise (fun i j=>Commute (product (t i) f) (product (t j) f)):= by
      intro i hi j hj hh
      refine moves (t i) f _ (hc.mono (ht i hi)) (fun a ha=> (moves (t j) f _ (hc.mono (ht j hj)) (fun b hb=> (?_))).symm)
      exact (hc (ht _ hi ha) (ht _ hj hb) (fun hv=> Finset.disjoint_left.mp (h hi hj hh) ha (hv ▸ hb))).symm
    rw [product_insert _ hj H, ← ih (h.mono hh) (hc.mono hq), Finset.biUnion_insert, union_commutes]; swap
    · intro a ha b hb hab; exact hc (by rw [Finset.biUnion_insert]; exact ha) (by rw [Finset.biUnion_insert]; exact hb) hab
    refine Finset.disjoint_left.mpr (fun i hi hk=>?_); obtain ⟨l,hl,hL⟩:=Finset.mem_biUnion.mp hk; exact Finset.disjoint_left.mp (h (show j∈(p:Set J) by simp [p]) (hh hl) (fun e=>hj (e ▸ hl))) hi hL
variable [Ring B]
omit [DecidableEq I] [DecidableEq J] in
lemma mapped (s:Finset I)(p:I→A)(f:A →+* B) : f (product s p)= product s (f ∘ p) := by
   let e:= (Fintype.equivFin s).symm; let L:List A:= List.ofFn (fun i => p (e i)); change f L.prod= (List.ofFn (fun i=> f (p (e i)))).prod; rw [map_list_prod]; unfold L; rw [List.map_ofFn]; rfl

end Ring
omit [DecidableEq I] in -- if actually used product
lemma product_true [CommRing A] (s : Finset I)(f : I→A) : product s f = s.prod f := by
  rw [actual s f (fun i _ j _ _=>Commute.all _ _ ),Finset.noncommProd_eq_prod]
end YM.Contacts.Ordered
