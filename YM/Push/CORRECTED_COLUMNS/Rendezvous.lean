import YM.Push.CORRECTED_COLUMNS.Pieces
/-!
# Exact merging of failed-mask h in the forced gas

Activated at most once per cube and all external constraints retained.
No assertion that inflation is cheap from this identity. Algebra includes
all physical marks; zero divisors permitted. `tsum` manipulations here
with old absolute convergence; next file ALSO gives actual absolute
convergence with prices for the new expression before any applications.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.UnionK
open Function Set Filter RG Wilson Lattice Marker Relation
open Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {n : Side} {G : Gauge} {V A : Type*} [DecidableEq V] [DecidableEq A] {R : Census V}
variable {P : Rep G n} {v : V → Site n} (L : Original P v R) (Q : AddedHeads P v R A)

def merge (p : Finset ℕ × Finset A) := p.1.disjSum p.2
def split (a : Finset (ℕ ⊕ A)) : Finset ℕ × Finset A := (a.toLeft,a.toRight)

private lemma combine (J : Finset (Piece Q)) :
    inventory P (J.biUnion Subtype.val)=J.biUnion (fun p => inventory P p.val) := by
  ext x; unfold inventory; rw [Finset.mem_biUnion,Finset.mem_biUnion]; constructor
  · rintro ⟨i,h,hi⟩; obtain ⟨p,hp,H⟩ := mem_biUnion.mp (mem_toLeft.mp h)
    exact ⟨p,hp,mem_biUnion.mpr ⟨i,mem_toLeft.mpr H,hi⟩⟩
  rintro ⟨p,hp,ht⟩; obtain ⟨i,hi,H⟩ := mem_biUnion.mp ht
  exact ⟨i,mem_toLeft.mpr (mem_biUnion.mpr ⟨p,hp,mem_toLeft.mp hi⟩),H⟩

lemma wrapped (J : Finset (Piece Q)) (hv : (J:Set (Piece Q)).PairwiseDisjoint fun p => unionOf Q p.val) :
    Ac.Parts (patch Q) (J.biUnion Subtype.val)=J.image Subtype.val := by
  classical
  let K := J.image Subtype.val
  have he : J.biUnion Subtype.val=K.biUnion id := by ext1; simp [K]
  rw [he]; apply Ac.separates
  · intro v hv; obtain ⟨p,hp,rfl⟩ := mem_image.mp hv; exact p.property.1
  intro p hp i hi h
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hp
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hi
  exact hv ha hb (fun w => h (congr_arg Subtype.val w))

private def duet (p : Finset ℕ × Finset A) (U : Config G n) :=
    oldEval L p.1 U * ∏ i∈p.2,Q.value i U

section
open scoped Classical

-- restore old constraints on any particular term before splitting its product
private lemma intact (J : Finset (Piece Q)) (U : Config G n) (h : lives Q J U) :
    P.activities.admissible P.p U (J.biUnion Subtype.val).toLeft := by
  refine ⟨?_, (combine Q J).trans h.2⟩
  intro i hi j hj hh
  obtain ⟨p,hp,hP⟩ := mem_biUnion.mp (mem_toLeft.mp hi)
  obtain ⟨q,hq,hQ⟩ := mem_biUnion.mp (mem_toLeft.mp hj)
  by_cases e : p=q
  · subst q
    exact p.property.2.2 (mem_toLeft.mpr hP) (mem_toLeft.mpr hQ) hh
  exact disjoint_left.mpr fun x hx hv => disjoint_left.mp (h.1 hp hq e)
    (mem_biUnion.mpr ⟨_,hP,hx⟩) (mem_biUnion.mpr ⟨_,hQ,hv⟩)

private lemma charge (J : Finset (Piece Q)) (U : Config G n) (h : lives Q J U) (ha : ∀ i∈J, actual i U) :
    duet L Q (split (J.biUnion Subtype.val)) U=newEval L Q J U := by
  unfold duet oldEval split newEval
  rw [if_pos h,if_pos (intact Q J U h)]
  change (∏ x∈ (J.biUnion Subtype.val).toLeft, value L Q (Sum.inl x) U)*(∏ x∈ (J.biUnion Subtype.val).toRight, value L Q (Sum.inr x) U)=_
  rw [← show (∏ i∈J.biUnion Subtype.val, value L Q i U) = _ from
      (prod_sum_eq_prod_toLeft_mul_prod_toRight (J.biUnion Subtype.val) (fun i => value L Q i U)), Finset.prod_biUnion]
  · refine prod_congr rfl fun i hi => ?_; rw [activated,if_pos (ha i hi)]
  intro p hp q hq e
  apply Finset.disjoint_left.mpr; intro i hi hj
  obtain ⟨x,hx⟩ := present Q i
  exact disjoint_left.mp (h.1 hp hq e) (mem_biUnion.mpr ⟨i,hi,hx⟩) (mem_biUnion.mpr ⟨i,hj,hx⟩)

private lemma full_of_meeting (J : Finset ℕ × Finset A) (U : Config G n) (H : duet L Q J U≠0) :
    ∃ s : Finset (Piece Q), lives Q s U ∧ (∀ i∈s, actual i U) ∧ s.biUnion Subtype.val=merge J := by
  let x := merge J
  let D := patch Q
  have ha : P.activities.admissible P.p U x.toLeft := by
    have hv : P.activities.admissible P.p U J.1 := by
      by_contra w; apply H; unfold duet oldEval; rw [if_neg w,zero_mul]
    simpa only [x,merge,toLeft_disjSum] using hv
  have hx : duet L Q J U=∏ i∈x,value L Q i U := by
    unfold duet oldEval; rw [if_pos (show P.activities.admissible P.p U J.1 by simpa only [x,merge,toLeft_disjSum] using ha)]
    exact (prod_disjSum J.1 J.2 (fun i => value L Q i U)).symm
  have hu (a) (h : a∈x) : value L Q a U ≠ 0 := fun w => H (hx.trans (prod_eq_zero h w))
  let E := Ac.Parts D x
  have hv (p : Finset (ℕ ⊕ A)) (hp : p ∈ E) : Joining Q p := by
    have ht := Ac.lives D x hp
    refine ⟨ht.2,?_,?_⟩
    · obtain ⟨i,hi⟩ := ht.2.1; cases i with
      | inl i => exact ⟨i,mem_toLeft.mpr hi⟩
      | inr i =>
        obtain ⟨s,hs,hU⟩ := Finset.not_disjoint_iff.mp (show ¬Healthy P.p.threshold (Q.support i) U from
          fun w => hu _ (ht.1 hi) (Q.fails i U w))
        have hz : s∈inventory P x := by
          unfold inventory; rw [ha.2]; exact hU
        obtain ⟨b,hb,Hb⟩ := mem_biUnion.mp hz
        have hw := Ac.contains D hp (Sum.inr i) hi
        have hy : Sum.inl b∈Ac.burst D x (Sum.inr i) := (Ac.bright ..).mpr ⟨mem_toLeft.mp hb,
          Relation.ReflTransGen.single ⟨ht.1 hi,mem_toLeft.mp hb,s,hs,(P.activities.forced _).inventory_sup Hb⟩⟩
        rw [hw] at hy
        exact ⟨b,mem_toLeft.mpr hy⟩
    intro i hi j hj h; exact ha.1 (mem_toLeft.mpr (ht.1 (mem_toLeft.mp hi)))
      (mem_toLeft.mpr (ht.1 (mem_toLeft.mp hj))) h
  let j (i : ↥E) : Piece Q := ⟨i.val,hv i.val i.property⟩
  let s := Finset.univ.image j
  have he : s.biUnion Subtype.val=x := by
    rw [← show E.biUnion id=x from Ac.reconstruct ..]; unfold s; ext y; simp [j]; constructor
    · rintro ⟨a,ha,hb,h⟩; exact ⟨a,ha,h⟩
    rintro ⟨a,ha,h⟩; exact ⟨a,ha,hv a ha,h⟩
  have hL : lives Q s U := by
    constructor
    · rintro i hi u hu h
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hi; obtain ⟨r,hr,rfl⟩ := mem_image.mp hu
      exact Ac.separate D x v.property r.property (fun w => h (Subtype.ext w))
    rw [← combine Q s,he]; exact ha.2
  refine ⟨s,hL,?_,he⟩
  intro i hi
  unfold actual; ext w; rw [Finset.mem_inter]; constructor
  · rintro ⟨hw,hp⟩; rw [← hL.2] at hp
    obtain ⟨y,hy,hh⟩ := mem_biUnion.mp hp
    by_cases e : i=y
    · exact e.symm ▸ hh
    exact False.elim (disjoint_left.mp (hL.1 hi hy e) hw (sized _ hh))
  intro hh; rw [← hL.2]; exact ⟨sized i hh,mem_biUnion.mpr ⟨i,hi,hh⟩⟩

private lemma price_exact (U : Config G n) :
    (∑' p,duet L Q p U)=∑' J,newEval L Q J U := by
  let S := Function.support fun J => newEval L Q J U
  have hi (x : S) : lives Q x.val U := by
    by_contra h
    exact x.property (show newEval L Q _ U=0 from if_neg h)
  have he (x : S) p (hp : p∈x.val) : actual p U := by
    by_contra h; exact x.property (by
      change newEval L Q x.val U=0
      unfold newEval; rw [if_pos (hi x)]; apply prod_eq_zero hp
      exact if_neg h)
  let f (x : S) := x.val.biUnion Subtype.val
  refine tsum_eq_tsum_of_ne_zero_bij (fun x : S => split (f x)) ?_ ?_ fun x => charge L Q _ _ (hi x) (he x)
  · intro x y h; apply Subtype.ext
    have hx : f x=f y := by
      have hE := congr_arg merge h
      simpa only [split,merge,toLeft_disjSum_toRight] using hE
    apply Finset.image_injective (f:= (Subtype.val : Piece Q → _)) Subtype.val_injective
    exact (wrapped Q _ (hi x).1).symm.trans ((congr_arg (Ac.Parts (patch Q)) hx).trans (wrapped Q _ (hi y).1))
  intro a ha
  change duet L Q a U≠0 at ha
  obtain ⟨s,hs,hp,h⟩ := full_of_meeting L Q a U ha
  have ht : split (s.biUnion Subtype.val)=a := by rw [h]; simp [split,merge]
  exact ⟨⟨s,fun w => ha ((congr_arg (fun a => duet L Q a U) ht.symm).trans
      ((charge L Q _ U hs hp).trans w))
    ⟩,ht⟩
end
section
variable [Fintype A]
-- regroup actual ordered sums, not replacing polynomial stress norms
-- by any false product of successive marker pushes
lemma rassemble (U : Config G n) (h : Summable fun b => ‖oldEval L b U‖) :
    (∑' b,oldEval L b U)*(∏ i, (1+Q.value i U))=∑' b,newEval L Q b U := by
  classical
  rw [← price_exact]
  have hp : Summable fun j => duet L Q j U := by
    -- finite on 2nd summation. no NormedRing, use finite-dimensional continuity bounds
    apply Summable.of_norm; rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun i => (hasSum_fintype _).summable,?_⟩
    simp_rw [tsum_fintype]
    refine summable_sum (s:= Finset.univ) fun s _ => ?_
    let C (s : Finset A) := ∏ j∈s,Q.value j U
    let P := LinearMap.toContinuousLinearMap (Algebra.lmul ℂ _ (C s))
    refine (h.mul_left ‖P‖).of_nonneg_of_le (fun i => norm_nonneg _) ?_
    intro b
    unfold duet
    rw [mul_comm]
    exact P.le_opNorm _
  letI : IsTopologicalSemiring (Poly R) := {}
  rw [hp.tsum_prod, ← Summable.tsum_mul_right _ h.of_norm]
  refine tsum_congr fun b => ?_; rw [Finset.prod_one_add,Finset.mul_sum,tsum_fintype,Finset.powerset_univ]; rfl
end
end YM.Push.Corrected.UnionK
