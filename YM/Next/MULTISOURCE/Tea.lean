import YM.Next.MULTISOURCE.Curves
import YM.Next.MULTISOURCE.Grades

/-! integrate finite polynomials coefficientwise. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open MvPolynomial RG Wilson Lattice Finset Filter MeasureTheory Reservoir
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I X : Type*} [DecidableEq I]

section
variable {F G : X → Wave I}
open scoped Pointwise
omit [DecidableEq I] in
lemma listed_fix (p : Wave I) : listed fun _ : X => p := ⟨_,fun _ => subset_refl _⟩
omit [DecidableEq I] in
lemma listed_C (f : X→ℂ) : listed fun x => (C (f x) : Wave I) := ⟨{0},fun _ => support_monomial_subset⟩
omit [DecidableEq I] in
lemma listed_smul (f : X → ℂ) (h : listed F) : listed fun i => f i • F i :=
  ⟨_,fun i => subset_trans support_smul (h.choose_spec i)⟩
lemma listed_add (h : listed F) (he : listed G) : listed fun i => F i + G i :=
  ⟨_,fun i => subset_trans support_add (union_subset_union (h.choose_spec i) (he.choose_spec i))⟩
lemma listed_mul (h : listed F) (he : listed G) : listed fun i => F i * G i :=
  ⟨h.choose + he.choose,fun i => subset_trans (support_mul ..) (Finset.add_subset_add (h.choose_spec i) (he.choose_spec i))⟩
lemma listed_pow (h : listed F) (k : ℕ) : listed fun i => F i^k := by
  induction k with
  | zero => simp only [pow_zero]; exact listed_fix 1
  | succ k ih => simp only [pow_succ]; exact listed_mul ih h
omit [DecidableEq I] in
lemma listed_if (p : X → Prop) [DecidablePred p] (h : listed F) : listed fun i => if p i then F i else 0 := by
  refine ⟨h.choose, fun i => ?_⟩
  dsimp only; split
  · exact h.choose_spec i
  simp
variable {J : Type*}
-- choose one uniform bound over all configurations.
omit [DecidableEq I] in
lemma listed_sum (s : Finset J) (F : J → X → Wave I) (h : ∀ i, listed (F i)) : listed fun x => ∑ i∈s,F i x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [sum_empty]; exact listed_fix _
  | insert i s hi ih => simp only [sum_insert hi]; exact listed_add (h i) ih
omit [DecidableEq I] in
lemma listed_prod (s : Finset J) (F : J → X → Wave I) (h : ∀ i, listed (F i)) : listed fun x => ∏ i∈s,F i x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [prod_empty]; exact listed_fix _
  | insert i s hi ih => simp only [prod_insert hi]; exact listed_mul (h i) ih
end

variable {G : Gauge} {c f : Side}

lemma list_push (S : StepData c f) (b : ℝ) (h : S.IsKernel b G) (F : Config G f → Wave I)
    (he : listed F) [Fintype I] (hh : ∀ z : I→ℂ, Integrable (fun U => eval z (F U)) (prior G _)) (V : Config G c) :
    ∃ p : Wave I, (∀ z,eval z p=S.push b (fun U => eval z (F U)) V) ∧
      ∀ t, coeff t p=S.push b (fun U => coeff t (F U)) V := by
  obtain ⟨T,hT⟩ := he
  have hp (q) : Integrable (fun U => coeff q (F U)) (prior G _) := by
    obtain ⟨N,hN,hq,hx⟩ := span T q
    let r (_ : I) : ℝ := 1
    have he (U : Config G f) := display r q (N:=N) (F U) hN (price_pos _ _ (fun _ _ => zero_lt_one)) hq (fun y hy => hx y (hT U hy))
    simp_rw [he]; exact integrable_finsetSum _ fun i _ => (hh _).const_mul _
  let X (t : Grade I) (U) := coeff t (F U)
  refine ⟨∑ j∈T,MvPolynomial.monomial j (S.push b (X j) V),?_,?_⟩
  · intro z; simp_rw [map_sum,eval_monomial]
    let Y (t : Grade I) := t.prod fun j k => z j ^ k
    have he (U : Config G f) : eval z (F U) = ∑ i∈T,X i U * Y i := by
      rw [MvPolynomial.eval_eq]; apply sum_subset (hT U)
      intro a _ ha; rw [notMem_support_iff.mp ha, zero_mul]
    simp_rw [he]; unfold StepData.push
    simp_rw [Finset.smul_sum,← smul_mul_assoc]
    -- commutation of real smul and complex multiplication
    have hg (t) : Integrable (fun U : Config G f => S.density b U V • (X t U)) (prior G _) :=
      StepData.push_slice h V (X t) (hp t)
    rw [integral_finsetSum]; swap; exact fun i _ => (hg i).mul_const _
    exact sum_congr rfl fun i hi => (integral_mul_const _ _).symm
  intro t; rw [coeff_sum, sum_eq_single t]
  · simp [X]
  · intro i _ h; simp [h]
  intro hh; unfold StepData.push
  simp [X, notMem_support_iff.mp (show t ∉ (F _).support from fun H => hh (hT _ H))]
end YM.Multi.Desk
