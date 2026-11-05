import YM.Analysis.Polydisc
import YM.Push.FREE_RESOLVENT.Gap
import YM.Push.FREE_RESOLVENT.Polar


/-!
# Chart projections and full positive coordinates

Identity-complete the constrained precision and include the shift on that
identity too. The root-chart kernel itself can still use zero *extension*
as required for tangent probes; exact factors below. Use for comparing at
changed tags after forgetting labels but not before retaining the two
references to the gauge data. No Dirichlet inversion at an arbitrary exterior
field is asserted here; only the indicated counting submatrices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix Filter Function Mark TestD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

namespace Shell
variable (e : β ↪ α)

def rim : Matrix α α ℝ := insertion e*(insertion e).transpose
def off : Matrix α α ℝ := 1-rim e

/-- Full size affine Gram completed to I. Leave off identity when returning
only the slice covariance. -/
def slice (A : Matrix α α ℝ) := rim e*A*rim e
def pad (A : Matrix α α ℝ) := slice e A + off e

omit [Fintype β] in
lemma pin : (insertion e).transpose * insertion e = 1 := insertion.orthogonal _ e.injective
omit [DecidableEq β] in
lemma sliced (A : Matrix α α ℝ) : slice e A = insertion e*(A.submatrix e e)*(insertion e).transpose := by
  rw [slice,rim,← insertion.compress]; simp only [Matrix.mul_assoc]

omit [Fintype α] [DecidableEq β] in
lemma clockwise : (rim e).transpose=rim e := by rw [rim,Matrix.transpose_mul,transpose_transpose]
omit [Fintype α] [DecidableEq β] in
lemma undo : (off e).transpose=off e := by rw [off,transpose_sub,transpose_one,clockwise]
lemma on_on : rim e * rim e=rim e := by
  unfold rim; rw [Matrix.mul_assoc,← Matrix.mul_assoc (insertion e).transpose,pin, Matrix.one_mul]
lemma off_off : off e*off e=off e := by unfold off; rw [Matrix.sub_mul, Matrix.mul_sub (rim e), on_on,Matrix.mul_one,sub_self,Matrix.one_mul]; simp


lemma enters : rim e*insertion e=insertion e := by
  rw [rim,Matrix.mul_assoc,pin,Matrix.mul_one]
lemma barred : off e*insertion e=0 := by rw [off, Matrix.sub_mul,Matrix.one_mul,enters,sub_self]
lemma barred_left : (insertion e).transpose*off e=0 := by rw [← undo,← Matrix.transpose_mul, barred]; simp
lemma reaches (A : Matrix α α ℝ) : (pad e A).submatrix e e=A.submatrix e e := by
  rw [← insertion.compress, pad,sliced,Matrix.mul_add, Matrix.add_mul,Matrix.mul_assoc (insertion e).transpose _ _]
  simp [Matrix.mul_assoc,pin,barred_left]; rw [← Matrix.mul_assoc,pin]; simp

-- defeq insertion (coerced). Full determinant not needed.
lemma gap {A : Matrix α α ℝ} {r : ℝ} (h : Gap (A.submatrix e e) r) : Gap (pad e A) (min r 1) := by
  constructor; intro v
  let b := (insertion e).transpose *ᵥ v
  let x := off e *ᵥ v
  have hw : dotProduct x x=dotProduct v x := calc
    _ = dotProduct v ((off e).transpose *ᵥ x) := by rw [dotProduct_transpose_mulVec]
    _ = _ := by rw [undo]; unfold x; rw [Matrix.mulVec_mulVec,off_off]
  have hv : dotProduct v v = dotProduct b b + dotProduct x x := calc
    _ = dotProduct v (insertion e *ᵥ b+x) := by
      congr 1; unfold b x off rim; rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec v,Matrix.one_mulVec]; abel
    _ = _ := by
      rw [dotProduct_add, hw]
      congr 1
      calc dotProduct v _ = dotProduct (insertion e *ᵥ b) v := dotProduct_comm ..
           _ = dotProduct b b := insertion.dot_push ..
  have hx : dotProduct v (slice e A *ᵥ v)=dotProduct b (A.submatrix e e *ᵥ b) := by
    rw [sliced,← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_comm v]; exact insertion.dot_push _ _ _ |>.trans (dotProduct_comm ..)
  rw [pad,Matrix.add_mulVec,dotProduct_add,hx,show dotProduct v (off e*ᵥ v)=_ from hw.symm,hv,mul_add]
  exact add_le_add ((mul_le_mul_of_nonneg_right (min_le_left ..) (normSum_nn b)).trans (h.lower b))
    (mul_le_of_le_one_left (normSum_nn x) (min_le_right ..))





-- entry mask (including inverse kernels on trees). Proof no color sup assumptions.
open scoped Classical in
lemma indicator (i j : α) : rim e i j = if i=j ∧ i ∈ Set.range e then 1 else 0 := by
  classical
  by_cases he : i=j
  · subst j; by_cases H : i∈ Set.range e
    · obtain ⟨a,rfl⟩ := H
      have hv := enters e
      -- simpler explicit
      rw [if_pos (by simp), rim]
      simp [Matrix.mul_apply,insertion,e.injective.eq_iff]
    rw [if_neg (not_and_of_not_right _ H)]
    unfold rim; refine Finset.sum_eq_zero fun j _ => ?_; simp [insertion,show e j≠i from fun h => H ⟨j,h⟩]
  rw [if_neg (by simp [he])]; unfold rim; refine Finset.sum_eq_zero fun k _ => ?_; unfold insertion; simp only [transpose_apply, of_apply]
  by_cases e k = i <;> simp [*]
open scoped Classical in
lemma off_test (i j : α) : off e i j = if i=j ∧ i ∉ Set.range e then 1 else 0 := by
  classical
  rw [off,Matrix.sub_apply,Matrix.one_apply, indicator]; split_ifs <;> grind
open scoped Classical in
lemma slice_test (A : Matrix α α ℝ) (i j) : slice e A i j = if i ∈ Set.range e ∧ j ∈ Set.range e then A i j else 0 := by
  classical
  split
  next h =>
    obtain ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩ := h
    have he : pad e A (e a) (e b)= A (e a) (e b) := congr_fun (congr_fun (reaches e A) a) b
    rw [pad,Matrix.add_apply,off_test] at he; simpa using he
  next h =>
    unfold slice; rw [Matrix.mul_apply]; refine Finset.sum_eq_zero fun k _ => ?_
    rcases not_and_or.mp h with h|h
    · apply mul_eq_zero_of_left; rw [Matrix.mul_apply]; refine Finset.sum_eq_zero fun w _ => ?_
      rw [indicator,if_neg (not_and_of_not_right _ h),zero_mul]
    apply mul_eq_zero_of_right; rw [indicator,if_neg]; rintro ⟨rfl,h'⟩; exact h h'

end Shell
end YM.FreeResolvent
