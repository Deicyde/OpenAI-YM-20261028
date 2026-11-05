import YM.Contacts.Score.Tag
/-!
# Stated local recursion, splitting alternatives

Pointwise already, without using integration-variable changes. Includes joint readings
of multiple disjoint group operations in the indicated patches, and the identity allowing
separated subgroups to be inserted while also evaluating the other groups.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule Ordered MultipleContact MultipleContact.Script
open scoped Topology BigOperators Classical ContDiff TensorProduct InnerProductSpace
variable {k : ℕ} {A : Type} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (P : E →ₗᵢ[ℝ] Points k)
namespace System
section alternatives
variable [CommRing F] [Algebra ℂ F] (S : System E F k) (s : ℝ) (g : Group k)
abbrev Arm := Option (Fin (S.depth g))
def needle (w : Fin (S.depth g)) := (S.depth g) - 1 - w.val
def weighedSum := ∑ w:Fin (S.depth g), S.reader g w
def treatment (v : S.Arm g) : E→ F →ₗ[ℂ] F := match v with
| some w=> S.reader g w
| none => (fun _=> LinearMap.id) - S.weighedSum g
def maskAt (v : S.Arm g) : Optical E:= match v with
| some w=> deviation (normalOn P g) s (S.needle g w)
| none=>LinearMap.id
omit [FiniteDimensional ℝ E] in
lemma sum_shape {I : Type*} (p:Finset I)(F' : I→ E→ F→ₗ[ℂ] F)(t : Score E F) : reshape (∑ i∈p,F' i) t = ∑ i∈p,reshape (F' i) t:= by
   induction p using Finset.induction_on with
   | empty=> rw [Finset.sum_empty,Finset.sum_empty,reshape_zero]
   | insert i p hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,reshape_add,ih]
lemma branches {X : Score E F} : X + S.subtractAt P s g X=
      ∑ v:S.Arm g, reshape (S.treatment g v) X * instructionScore E F (S.maskAt P s g v) := by
  rw [Fintype.sum_option]
  let L := S.weighedSum g; let Y := (fun _ : E=> (LinearMap.id : F →ₗ[ℂ] F))
  let R(v : Fin (S.depth g)):= S.reader g (v:ℕ); let w:=taylor (normalOn P g) s
  change _= reshape (Y-L) X*(1: Score E F) + ∑ v:Fin (S.depth g), reshape (R v) X* instructionScore E F (deviation _ _ _); rw [mul_one]
  have he:L= ∑ v:Fin (S.depth g),R v:=rfl; let D(v:Fin (S.depth g)):=w (S.needle g v); let e(v:Fin (S.depth g)):= instructionScore E F (D v); let f(v):= reshape (R v) X
  have hd(v:Fin (S.depth g)) : instructionScore E F (deviation (normalOn P g) s (S.needle g v)) = 1 - e v:= by exact TensorProduct.tmul_sub (1:E→F) (1:Optical E) (D v)
  have hh:= reshape_add (Y-L) L X; rw [sub_add_cancel, reshape_id] at hh
  unfold subtractAt; change X + -(∑ v:Fin (S.depth g),f v * e v)= _; simp_rw [hd,mul_sub,mul_one, Finset.sum_sub_distrib]; change _= reshape _ X+ ((∑ v: Fin (S.depth g),f v)-(∑ v:Fin (S.depth g), f v*e v)); rw [← add_sub_assoc, show ∑ v: Fin (S.depth g), f v = _ from (?_ : _= reshape L X),← hh]; rfl
  exact (sum_shape _ R _).symm
lemma full_split (h : 1 < g.card) : S.full P s g = ∑ v:S.Arm g,
     reshape (S.treatment g v) (S.punctured P s g)*instructionScore E F (S.maskAt P s g v):= by rw [full_formula P S _ _ (Finset.card_pos.mp (by omega)), S.equation_subtract P _ _ h]; exact branches ..

lemma holes (Q : Pieces g)(hm : plane g ≤ LinearMap.range P.toLinearMap) (v : SmoothTests E) (hg : g.Nonempty) (he : Q≠⊤)
   (hv : ∀ x∈ tsupport v.val,∀ i∈Q.parts,∀ j∈Q.parts,i≠j → ∀ a∈i, ∀ b∈j,(P x) a≠(P x) b) : ∀ x ∈ (normalOn P g)ᗮ, x∉ tsupport v.val:=by
   obtain ⟨i,hi,j,hj,h⟩:= many he hg; obtain ⟨a, ha⟩:= Q.nonempty_of_mem_parts hi; obtain ⟨b,hb⟩:= Q.nonempty_of_mem_parts hj
   intro x hx ht; apply hv x ht i hi j hj h a ha b hb; exact (collapsed_iff ..).1 ((local_collapse hm x).2 (Submodule.starProjection_apply_eq_zero_iff (normalOn P g)|>.2 hx)) _ (Q.subset hi ha) _ (Q.subset hj hb)

lemma departure (Q : Pieces g) (hm : plane g ≤ LinearMap.range P.toLinearMap) (v : SmoothTests E) (hg : g.Nonempty) (he : Q≠⊤)
   (hv : ∀ x∈ tsupport v.val,∀ i∈Q.parts,∀ j∈Q.parts,i≠j → ∀ a∈i, ∀ b∈j,(P x) a≠(P x) b) :
   S.punctured P s g*instructionScore E F (mask v)=parcel (S.full P s) Q*instructionScore E F (mask v) := by
   rw [← S.refines P s g v Q hm hv,full_formula P _ _ _ hg,add_mul, all_off (holes P g Q hm v hg he hv) (S.translatesOrigin P s g),add_zero]
end alternatives

variable (S : System E (Grammar A) k) (s : ℝ) {g : Group k}
local notation "ℱ" => Score E (Grammar A)
local notation "T!" => Board (Group k) A

def forest (x : Group k → ℱ) (Q : Pieces g) := parcel (fun i=> retag E (tag i) (x i)) Q
-- system param not binder; define within System with Dot later
def coupled (Q : Pieces g):= forest (S.full P s) Q
lemma knowTags: permitted (fun (i:Group k)=> retag E (tag i) (S.full P s i)) := fun a b h=>
     Mark.agree ((S.uses_full P s a).relabel (tag a)) ((S.uses_full P s b).relabel (tag b)) (fun _ _ ha hb=> ha.independent hb (normals_distinct P h))

def otherPlaces (Q : Pieces g) (i : Q.parts):= product (Q.parts.erase i.val) (fun j=> retag E (tag j) (S.full P s j))
-- replace i-th operation while keeping others in the same ambient integral
def portionAt (Q : Pieces g)(i : Q.parts)(X : Score E (Grammar A)) : Score E T! := S.otherPlaces P s Q i * retag E (tag i.val) X
lemma portion_comb (Q : Pieces g)(i : Q.parts) : S.coupled P s Q= S.portionAt P s Q i (S.full P s i.val):= split_last _ i.property _ ((S.knowTags P s).stands Q)
-- atomic alternative of i-root in forest (still on punctured distribution), pairing against whole test transformed by associated mask.
def opensRoot (Q : Pieces g)(i : Q.parts)(F : E→ Grammar A→ₗ[ℂ] Grammar A) := S.portionAt P s Q i (reshape F (S.punctured P s i.val))
lemma split_score (Q : Pieces g)(i : Q.parts)(hs : 1 < i.val.card):
   S.coupled P s Q = ∑ v:S.Arm i.val, S.opensRoot P s Q i (S.treatment i.val v) * instructionScore E (Board (Group k) A) (maskAt P S s i.val v) := by
   rw [S.portion_comb P s Q i,full_split P S s _ hs, portionAt,map_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun v _=> by simp_rw [opensRoot,portionAt,mul_assoc,← retag_rules (tag (A:=A) (i:Group k))]; rw [map_mul]
lemma separates_body (Q : Pieces g)(i : Q.parts)(hs: 1 < i.val.card)(f : SmoothTests E) (x:E) :
    action x f (S.coupled P s Q) = ∑ v:S.Arm i.val, action x (maskAt P S s i.val v f) (S.opensRoot P s Q i (S.treatment i.val v)):= by rw [S.split_score P s Q i hs,map_sum]; simp_rw [takeRight]

/-- Updating a reader from an i-group product/linearized choice to the child entries. -/
def review (Q : Pieces g)(i : Q.parts)(R : Pieces i.val) (F : Grammar A →ₗ[ℂ] Grammar A): T!→ₗ[ℂ] T! := appropriating R.parts ((tag i.val).toLinearMap.comp F)
lemma reader_shape (Q : Pieces g)(i : Q.parts)(R : Pieces i.val) (F : E→ Grammar A →ₗ[ℂ] Grammar A):
   S.portionAt P s Q i (reshape F (parcel (S.full P s) R))= reshape (fun x=>review Q i R (F x)) (S.coupled P s (replace i R)):= by
  let h : Group k→ Score E T!:= fun j=> retag E (tag j) (S.full P s j); let l:= Q.parts.erase i.val; let r:= R.parts; let f :=product l h; let J:=product r h
  have hh : S.coupled P s (replace i R)= f * J:=by change product (replace i R).parts h= _; have he:=(S.knowTags P s).stands (replace i R); rw [replace_parts] at he ⊢; exact union_commutes (replace_disj i R) h he
  have hx:= fork_without (r:Set (Group k)) l (Finset.disjoint_coe.mpr (replace_disj i R)) (S.full P s)
  have hv:= fork_inside (r:Set (Group k)) r (by rfl) (S.full P s)
  have ht:= rebuild_left (r:Set (Group k)) f J (fun (x:E)=> (tag i.val).toLinearMap.comp (F x)) hx hv
  rw [hh, portionAt, retags,reshape_composes]; exact ht.symm
lemma clipped (Q : Pieces g)(i : Q.parts)(R : Pieces i.val) (F : E→ Grammar A →ₗ[ℂ] Grammar A) (v : SmoothTests E) (hg : plane i.val ≤ LinearMap.range P.toLinearMap) (hr : R≠⊤)
    (hv : ∀ x∈ tsupport v.val,∀ i∈R.parts,∀ j∈R.parts,i≠j → ∀ a∈i, ∀ b∈j,(P x) a≠(P x) b) : S.opensRoot P s Q i F * instructionScore E T! (mask v)= reshape (fun x=> review Q i R (F x)) (S.coupled P s (replace i R)) * instructionScore E T! (mask v) := by
  rw [← S.reader_shape P s Q i R F]; unfold opensRoot portionAt; simp_rw [mul_assoc, ← retag_rules (tag (A:=A) i.val) (mask v),← map_mul, ← reshape_instruction]; rw [departure P _ _ _ R hg v (Q.nonempty_of_mem_parts i.property) hr hv]
omit [FiniteDimensional ℝ E] in
lemma replace_test {V W : Score E T!} (v : SmoothTests E) (x:E)(hv : V * instructionScore E T! (mask v) = W * instructionScore E T! (mask v)) : action x v V= action x v W := by
   let q: SmoothTests E:=⟨fun _=>1,(contDiff_const (c:=(1:ℂ)) : ContDiff ℝ ∞ (fun _:E=>(1:ℂ)))⟩
   have h:= congrArg (action x q) hv; rw [takeRight,takeRight] at h; exact (show mask v q=v from Subtype.ext (funext (fun x=> mul_one _))) ▸ h
lemma separated (Q : Pieces g)(i : Q.parts)(R : Pieces i.val) (F : E→ Grammar A →ₗ[ℂ] Grammar A) (v : SmoothTests E) (x:E) (hg : plane i.val ≤ LinearMap.range P.toLinearMap) (hr : R≠⊤)
    (hv : ∀ x∈ tsupport v.val,∀ i∈R.parts,∀ j∈R.parts,i≠j → ∀ a∈i, ∀ b∈j,(P x) a≠(P x) b) : action x v (S.opensRoot P s Q i F)= review Q i R (F x) (action x v (S.coupled P s (replace i R))) := by rw [← action_reshape (fun x=> review Q i R (F x))]; exact replace_test v x (S.clipped P s Q i R F v hg hr hv)
end System
end YM.Contacts.Normal
