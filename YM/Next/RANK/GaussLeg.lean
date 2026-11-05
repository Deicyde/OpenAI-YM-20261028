import YM.Next.RANK.GaussTrack

/-!
# Match moments to actual free leg kernel

Requires distinct points with actual Maxwell.kernel using normalized positions.
Off-diagonal curl derivatives. Canceled self contributions for each probed label.
No degree grading of fields in this identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Normal
open Maxwell Wick MvPolynomial Function Finset
open scoped Classical Topology BigOperators

variable {G : Gauge} {n : ℕ}

def frameX {x : Points n} (hx : x ∈ conf n) : Symmetric (Fin n × Slot G) where
  cov i j := if i.1=j.1 then 0 else entry i.2 j.2 (x i.1) (x j.1)
  symm i j := by
    by_cases hh : i.1=j.1
    · rw [if_pos hh, if_pos hh.symm]
    rw [if_neg hh,if_neg (Ne.symm hh)]; exact entry_symmetric _ _ ((show Injective x.ofLp from hx).ne hh)

namespace BasisMatch
open Maxwell.Wick.Occ

private lemma appears (W : Powers G n) : (∏ i,(rename fun y => (i,y)) (monBasis G (W i))) =
    glyphs (fun a : Occ W => (a.label,a.probe)) univ := by
  let A := (i : Fin n) × (v : (W i).support) × Fin (W i v.val)
  let f : A → Occ W := fun a => atSlot a.1 a.2.1.val a.2.2.val a.2.2.isLt
  have ht (a : Occ W) : a.probe ∈ (W a.label).support := Finsupp.mem_support_iff.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt a.legit))
  let e : A ≃ Occ W := {
    toFun := f
    invFun i := ⟨i.label,⟨i.probe,ht i⟩,i.index,i.legit⟩
    left_inv i := rfl
    right_inv i := rfl }
  let h (a : A) := (X (R:=ℂ) (a.1,a.2.1.val) : poly _)
  have hh (i : Fin n) : rename (fun y => (i,y)) (monBasis G (W i)) = ∏ v : (z : (W i).support) × Fin (W i z.val), h ⟨i,v⟩ := by
    rw [show monBasis G (W i) = MvPolynomial.monomial (W i) 1 from rfl,monomial_eq,map_one,one_mul,Finsupp.prod,map_prod,Fintype.prod_sigma]; simp_rw [map_pow,rename_X]
    rw [← Finset.prod_attach]; simp [h]
  simp_rw [hh]; rw [← Fintype.prod_sigma h]; exact Fintype.prod_equiv e _ _ (fun i => rfl)

lemma aglow {x : Points n} (hx : x ∈ conf n) (W : Powers G n) : Maxwell.Wick.monomial x W=
    blend (frameX hx) 0 (∏ i : Fin n, (rename (fun y => (i,y))) (monBasis G (W i))) := by
  let Z := fun a : Occ W => (a.label,a.probe)
  let q : Symmetric (Fin n × Slot G) := frameX hx
  have hs (a b : Occ W) (h : a.label=b.label) : q.cov (Z a) (Z b)=0 := if_pos h
  rw [appears, headed label _ _ hs]
  let loc := (label (W:=W))
  let Q := register loc univ
  change (∑ P : Matching W, Occ.graph x P)=∑ P ∈ Q, link loc q Z univ P
  refine sum_bij (fun i _ => partner i) ?_ ?_ ?_ ?_
  · intro i hi; obtain ⟨i,h1,h2⟩ := i
    exact mem_filter.mpr ⟨mem_univ _,h1,fun j _ => h2 j,fun j hu => False.elim (hu (mem_univ _))⟩
  · exact fun a _ b _ h => Subtype.ext h
  · intro i hi; obtain ⟨h,h1,h2,h3⟩ := mem_filter.mp hi
    refine ⟨⟨i,h1,fun j => h2 j (mem_univ _)⟩,mem_univ _,rfl⟩
  intro i _; unfold Occ.graph link
  refine prod_congr rfl fun a ha => ?_
  exact (if_neg (different i a).symm).symm
end BasisMatch

lemma Wick_reads {x : Points n} (hx : x∈conf n) (p : Fin n → WickPol G) : Wick.moment G x p =
    blend (frameX hx) 0 (∏ i, (rename (fun y => (i,y))) (p i)) := by
  let Q : Symmetric (Fin n × Slot G) := frameX hx
  let L := fun i : Fin n => (rename (R := ℂ) (fun v : Slot G => (i,v))).toLinearMap
  let w := ((blend Q 0).compMultilinearMap (MultilinearMap.mkPiAlgebra ℂ (Fin n) (poly (Fin n × Slot G)))).compLinearMap L
  change Wick.moment G x p = w p
  rw [Multilabel.expansion (fun _ => monBasis G) w, Multilabel.expansion (fun _ => monBasis G) (moment G x)]
  refine sum_congr rfl fun i _ => ?_
  rw [moment_basis]; exact congr_arg (_ • ·) (BasisMatch.aglow hx i)
end YM.Next.Rank.Normal
