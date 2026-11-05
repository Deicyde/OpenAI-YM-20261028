import YM.Contacts.Score.Formula
/-! # Tag with open-group names

Polynomials across strict multiple clusters. Names here are bookkeeping to retain
linear tests (of a complete word) through arbitrary numbers of projections etc.,
even when pairing with another cluster not itself yet estimated. They don't renormalize label
orientations. Use `eraseTags` / `retag` functions for the actual placements.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule Ordered MultipleContact MultipleContact.Script
open scoped Topology BigOperators Classical ContDiff TensorProduct InnerProductSpace
variable {I : Type} {A : Type} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Board (I A : Type) := Grammar (I × A)
def tag (i : I) : Grammar A →ₐ[ℂ] Board I A := MultipleContact.Script.rewrite (Prod.mk i)
def eraseTags : Board I A →ₐ[ℂ] Grammar A:= MultipleContact.Script.rewrite Prod.snd
@[simp] lemma set_tag (i : I) (x : A) : tag i (stamp x)=stamp (i,x) := rewrite_stamp ..
@[simp] lemma clear_tags (x : I×A) : eraseTags (stamp x) = stamp x.2 := rewrite_stamp ..
@[simp] lemma erase_tags (i:I) (x: Grammar A) : eraseTags (tag i x)=x:= by
    induction x using grammar_induction with
    | hm n p => unfold spell; rw [map_prod,map_prod]; simp
    | ha f g h k=> simp [map_add,h,k]
    | hs r f h=> simp [map_smul,h]

abbrev Rivet (I A : Type) := (Grammar A) ⊗[ℂ] (Board I A)
variable (T : Set I)
def inlet : Grammar A →ₐ[ℂ] Rivet I A := Algebra.TensorProduct.includeLeft
-- downstream retains its tags
def outlet : Board I A →ₐ[ℂ] Rivet I A := Algebra.TensorProduct.includeRight
private def grain (p : I×A) : Rivet I A := if p.1∈T then inlet (I:=I) (stamp p.2) else outlet (stamp p)
def fork : Board I A→ₐ[ℂ] Rivet I A := AddMonoidAlgebra.lift _ _ _ {
  toFun m := (m.toAdd.map (grain T)).prod
  map_mul' m n := by change ((m.toAdd+n.toAdd).map (grain T)).prod=_; rw [Multiset.map_add,Multiset.prod_add]
  map_one' := rfl }
lemma fork_to (p : I×A): fork T (stamp p) = if p.1∈T then inlet (I:=I) (stamp p.2) else outlet (stamp p):= by
   rw [fork,stamp,AddMonoidAlgebra.lift_single,one_smul]; exact Multiset.prod_singleton _
lemma fork_in (i:I)(hi:i∈T)(f:Grammar A): fork T (tag i f)= inlet f:=by
   induction f using grammar_induction with
   | hm n f=> unfold spell; rw [map_prod,map_prod,map_prod]; simp_rw [set_tag,fork_to,if_pos (show _ from hi)]
   | ha _ _ hx hy=> simp only [map_add,hx,hy]
   | hs r f hx=> simp only [map_smul,hx]
lemma fork_out (i:I)(hi:i∉T)(f:Grammar A): fork T (tag i f)=outlet (tag i f):=by
   induction f using grammar_induction with
   | hm n f=> unfold spell; rw [map_prod,map_prod,map_prod]; simp [fork_to,hi]
   | ha _ _ hx hy=> simp only [map_add,hx,hy]
   | hs r f hx=> simp only [map_smul,hx]

def welding (F : Grammar A→ₗ[ℂ] Board I A) : Rivet I A →ₗ[ℂ] Board I A := TensorProduct.lift ((LinearMap.mul ℂ (Board I A)).comp F)
lemma welding_piece (F : Grammar A→ₗ[ℂ] Board I A)(x : Grammar A)(y : Board I A) : welding F (x ⊗ₜ[ℂ] y)= F x * y:= TensorProduct.lift.tmul ..
def appropriating (F : Grammar A→ₗ[ℂ] Board I A) : Board I A→ₗ[ℂ] Board I A := (welding F).comp (fork T).toLinearMap
lemma weld_untouched (F : Grammar A→ₗ[ℂ] Board I A) {x y : Board I A} {z : Grammar A} (hx : fork T x=outlet x)(hy : fork T y=inlet z) : appropriating T F (x*y)= x * F z:= by
   change welding F (fork T (x*y))=_; rw [map_mul,hx,hy]; change welding F ((1 ⊗ₜ[ℂ] x)*(z ⊗ₜ[ℂ] 1))=_; rw [Algebra.TensorProduct.tmul_mul_tmul, welding_piece, one_mul,mul_one,mul_comm]

lemma retag_comp (P : Score E (Grammar A))(B : Type*) {C : Type*} [CommRing B] [CommRing C][Algebra ℂ B][Algebra ℂ C]
  (F : Grammar A→ₐ[ℂ] B) (G : B→ₐ[ℂ] C) : retag E (G.comp F) P= retag E G (retag E F P):= (reshape_composes (fun _=> F.toLinearMap) (fun _=>G.toLinearMap) P).symm
lemma reconnect (i:I) {B : Type*} [CommRing B] [Algebra ℂ B] (F : Board I A →ₐ[ℂ] B) (G : Grammar A →ₐ[ℂ] B) (h : ∀ f, F (tag i f) = G f) (p:Score E (Grammar A)) : retag E F (retag E (tag i) p)= retag E G p := by
   rw [← retag_comp p (Board I A)]; exact congrArg (fun A' : Grammar A →ₐ[ℂ] B=> retag E A' p) (AlgHom.ext h)
lemma fork_inside (s:Finset I)(h:(s:Set I) ⊆ T)(p : I→ Score E (Grammar A)) : retag E (fork T) (product s (fun i=> retag E (tag i) (p i)))= retag E inlet (product s p):= by
   rw [retag_product,retag_product]; exact eq_product fun i hi=> reconnect i _ _ (fork_in T i (h hi)) _
lemma fork_without (s:Finset I)(h:Disjoint (s:Set I) T)(p : I→ Score E (Grammar A)) : retag E (fork T) (product s (fun i=>retag E (tag i) (p i)))= retag E outlet (product s (fun i=>retag E (tag i) (p i))):= by
   rw [retag_product,retag_product]; exact eq_product fun i hi=> Eq.trans (reconnect i _ _ (fork_out T i fun he=> Set.disjoint_left.mp h hi he) _) (retag_comp (p i) (Board I A) _ outlet) -- typing F & G=?
-- generic assembly naturality (order retained in the optical factors)
lemma welding_of_formula {A B C:Type*}[CommRing A][Algebra ℂ A][CommRing B][Algebra ℂ B][CommRing C][Algebra ℂ C]
     (x : Score E B)(y : Score E A)(L : A →ₐ[ℂ] C) (R : B →ₐ[ℂ] C)(F : E→ A →ₗ[ℂ] B)(H : E→ C→ₗ[ℂ] B)
     (h : ∀ e a b,H e (R b*L a)= b*F e a): reshape H (retag E R x * retag E L y) = x*reshape F y:= by
   induction x using inductionScore with
   | h₀=>simp
   | h₁ V U=>
     induction y using inductionScore with
     | h₀=>simp
     | h₁ W T=> simp only [retags,reshape_tape,Algebra.TensorProduct.tmul_mul_tmul]; congr; funext i; exact h i (W i) (V i)
     | h₂ x y hx hy=> simp only [map_add,mul_add,hx,hy]
   | h₂ x y hx hy=> simp only [map_add,add_mul,hx,hy]
lemma fork_repairs (x : Score E (Board I A)) (y : Score E (Grammar A)) (a : E→ Grammar A→ₗ[ℂ] Board I A) :
    reshape (fun i=>welding (a i)) (retag E outlet x * retag E inlet y)= x*reshape a y:= by
   refine welding_of_formula x y inlet outlet a (fun i=>welding (a i)) ?_
   intro e c d
   change welding (a e) (((1:Grammar A) ⊗ₜ[ℂ] d)*(c ⊗ₜ[ℂ] (1:Board I A)))= _
   rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,mul_one,welding_piece,mul_comm]
lemma rebuild_left (k v : Score E (Board I A)) {z : Score E (Grammar A)}
     (F : E→ Grammar A →ₗ[ℂ] Board I A) (he : retag E (fork T) k=retag E outlet k)
     (hx : retag E (fork T) v=retag E inlet z) : reshape (fun x=>appropriating T (F x)) (k*v) = k*reshape F z:= by
   have h:= reshape_composes (fun (_:E)=> (fork T).toLinearMap) (fun x=>welding (F x)) (k*v)
   unfold appropriating; rw [← h, ← retags (fork T),map_mul,he,hx,fork_repairs]
end YM.Contacts.Normal
