import YM.Next.MULTISOURCE.Curves
import YM.Next.MULTISOURCE.Larger

/-! Local analytic readout cannot involve a parameter forgotten outside its slot. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open RG Marker Wilson Lattice MvPolynomial Filter Finset MeasureTheory Reservoir
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {I : Type*} [Fintype I] [DecidableEq I] {r : ℝ}

lemma sleeps (A : Set (I→ℂ)) (he : 0<r) (hi : boxes r ⊆ A) (x : I) (p : Wave I) (h : sleepy A x p)
    (q : Grade I) (hx : x∈q.support) : coeff q p=0 := by
  let F := p.support.filter fun q => x ∉ q.support
  let z : Wave I := ∑ i∈F,MvPolynomial.monomial i (coeff i p)
  have hh (V : I→ℂ) (hp : V∈ boxes r) : eval V p=eval V z := by
    let a := Function.update V x 0
    have ha (i : I) (h : i ≠ x) : a i=V i := Function.update_of_ne h ..
    rw [h _ (hi hp) a (hi (show a∈ boxes r from fun i => by
      by_cases e : i=x
      · simp [a,e,he.le]
      rw [ha _ e]; exact hp i)) (fun _ hi => (ha _ hi).symm), MvPolynomial.eval_eq]
    simp_rw [z,map_sum,MvPolynomial.eval_monomial,F,sum_filter,Finsupp.prod]
    apply Finset.sum_congr rfl; intro b hb; split
    · rename_i he
      refine congrArg₂ _ rfl (Finset.prod_congr rfl fun y hy => ?_); rw [ha _ (fun h => he (h ▸ hy))]
    rename_i hb; push Not at hb; rw [Finset.prod_eq_zero hb ?_,mul_zero]; simp [a, (Finsupp.mem_support_iff.mp hb)]
  have hB := converge (p-z) q (C:=0) (fun V hv => by rw [map_sub,hh V hv,sub_self,norm_zero]) he
  have hz : coeff q z=0 := by
    simp only [z, MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
    refine Finset.sum_eq_zero fun i hi => ?_
    split
    · rename_i hh; subst i; exact False.elim ((mem_filter.mp hi).2 hx)
    rfl
  rwa [MvPolynomial.coeff_sub,hz,sub_zero,mul_zero,norm_le_zero_iff] at hB
end YM.Multi.Desk
