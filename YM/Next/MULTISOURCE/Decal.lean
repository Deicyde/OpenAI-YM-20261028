import YM.Next.MULTISOURCE.Evaluate


/-!
# Passing from ordinary parameter polynomial to markers
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Desk
open RG Wilson Lattice Marker MvPolynomial Finset Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {I : Type*} [DecidableEq I] (R : Census I)

abbrev Grade (I : Type*) := I →₀ ℕ
abbrev Wave (I : Type*) := MvPolynomial I ℂ

def power (s : Finset I) : Grade I := s.sum fun i => Finsupp.single i 1
lemma power_apply (s : Finset I) (i : I) : power s i=if i∈ s then 1 else 0 := by
  unfold power; simp only [Finsupp.finsetSum_apply,Finsupp.single_apply]
  simp
omit [DecidableEq I] in
@[simp] lemma power_empty : power (∅: Finset I)=0 := by rw [power, sum_empty]
omit [DecidableEq I] in
@[simp] lemma power_single (i : I) : power {i}=Finsupp.single i 1 := by rw [power,sum_singleton]
@[simp] lemma support_power (s : Finset I) : (power s).support=s := by
  ext i; rw [Finsupp.mem_support_iff,power_apply]; by_cases h : i∈s <;> simp [h]
lemma print_erase (s : R.Mode) (i : I) (h : i∈s.val) : power s.val = power (s.val.erase i) + Finsupp.single i 1 := by
  unfold power; exact (add_sum_erase _ _ h).symm.trans (add_comm ..)

def print (R : Census I) : Wave I →ₐ[ℂ] Poly R := aeval fun i => Poly.send (R.fire i) 1

@[simp] lemma print_C (a : ℂ) : print R (C a) = Poly.send R.quiet a := (print R).commutes a
@[simp] lemma print_X (i : I) : print R (X i) = Poly.send (R.fire i) 1 := aeval_X ..

lemma print_coeff (p : Wave I) (t : R.Mode) : (print R p).part t = MvPolynomial.coeff (power t.val) p := by
  classical
  induction p using MvPolynomial.induction_on generalizing t with
  | C a =>
    by_cases h : t=R.quiet
    · rw [print_C]; simp [h, Census.quiet]
    have ht : power t.val ≠ 0 := fun e => h (Subtype.ext (by change _=∅; rw [← support_power t.val, e]; simp))
    rw [print_C, MvPolynomial.coeff_C_of_ne_zero ht]; simp [h]
  | add p q h k => simp [h,k]
  | mul_X p i H =>
    rw [map_mul, print_X, Poly.part_mul]
    have he (s : R.Mode) : (∑ j : R.Mode, if Poly.merges s j t then (print R p).part s * (Poly.send (R.fire i) 1).part j else 0) =
        if Poly.merges s (R.fire i) t then (print R p).part s else 0 := by
      rw [sum_eq_single (R.fire i)]; simp
      · intro b _ hb; simp [hb]
      simp
    simp_rw [he]
    by_cases h : i∈t.val
    · let w : R.Mode := ⟨t.val.erase i,R.down t.property _ (erase_subset ..)⟩
      have ht : Poly.merges w (R.fire i) t := ⟨by simp [Census.fire,w],by simp [w,Census.fire,h]⟩
      rw [print_erase R t i h,coeff_mul_X]; rw [← H w]
      rw [sum_eq_single w,if_pos ht]
      · intro b _ hb; rw [if_neg]; intro ⟨hf,hg⟩
        have hh : i ∉ b.val := fun e => Finset.disjoint_left.mp hf e (Finset.mem_singleton_self _)
        apply hb; refine Subtype.ext ?_; change _ = t.val.erase i
        rw [← hg]; simp [Census.fire, hh]
      simp
    rw [coeff_mul_X', support_power, if_neg h]; apply sum_eq_zero
    intro b _; rw [if_neg]; intro ⟨hf,hg⟩; apply h; rw [← hg]; exact mem_union_right _ (mem_singleton_self _)

section
variable [Fintype I]

def staves (a : I → ℂ) : Wave I := ∑ i,a i • X i
omit [DecidableEq I] in
lemma staves_eval (a z : I → ℂ) : eval z (staves a) = ∑ i,z i*a i := by
  unfold staves; rw [map_sum]; simp_rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C,eval_X,mul_comm (a _)]
lemma staves_print (a : I → ℂ) : print R (staves a) = lambda R a := by
  unfold staves lambda; rw [map_sum]; apply sum_congr rfl; intro i _
  rw [map_smul,print_X]; ext t; by_cases h : t=R.fire i <;> simp [h]
include R in
lemma staves_zero (a : I → ℂ) : coeff 0 (staves a)=0 := by
  have h := print_coeff R (staves a) R.quiet
  simp only [Census.quiet, power_empty] at h
  exact h.symm.trans (by rw [staves_print]; exact lambda_quiet _)

-- Uniform polynomial approximations below use this map

def vapor (B : ℕ) (p : Wave I) := ∑ j∈Finset.range (B+1),(j.factorial:ℂ)⁻¹ • p^j
lemma vapor_print {p : Wave I} (B : ℕ) (h : Fintype.card I ≤ B) (hv : coeff 0 p=0) :
    print R (vapor B p)=Poly.pass (print R p) := by
  have ht : (print R p).part R.quiet=0 := by rw [print_coeff]; simp only [Census.quiet,power_empty]; exact hv
  rw [pass_extended _ ht h]; simp [vapor]
omit [Fintype I] [DecidableEq I] in
lemma vapor_eval (B : ℕ) (p : Wave I) (z : I → ℂ) : eval z (vapor B p) =
    ∑ i ∈ Finset.range (B+1), (eval z p)^i / (i.factorial:ℂ) := by
  unfold vapor; rw [map_sum]; refine sum_congr rfl ?_; intro i _
  rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, map_pow]; simp only [div_eq_mul_inv, mul_comm]
end
end YM.Multi.Desk
