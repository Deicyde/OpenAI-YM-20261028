import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import YM.Push.FREE_RESOLVENT.Weights


/-!
# Precision gap in counting coordinates

Explicit real dot products. Use accretivity (quadratic form) so symmetric
compressions inherit it and diagonal tilts can keep using the same API.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix
open scoped BigOperators
variable {ι κ : Type*} {X : Type*}

/-- Push index by `e`, for an injection this embeds with zeroes in unoccupied
coordinates. Exact matrix to avoid changing the Gram operator outside a window
when selecting a principal compression. -/
def insertion [DecidableEq ι] (e : κ → ι) : Matrix ι κ ℝ :=
  of fun i j => if e j = i then 1 else 0

namespace insertion
variable {ν : Type*} [DecidableEq ι] (e : κ → ι)

lemma transpose_mul [Fintype ι] (A : Matrix ι ν ℝ) :
    (insertion e).transpose * A = A.submatrix e id := by
  ext; simp [Matrix.mul_apply,insertion,ite_mul]
lemma mul [Fintype ι] (A : Matrix ν ι ℝ) :
    A * insertion e = A.submatrix id e := by
  ext; simp [Matrix.mul_apply,insertion,mul_ite]
lemma compress [Fintype ι] (A : Matrix ι ι ℝ) :
    (insertion e).transpose * A * insertion e = A.submatrix e e := by
  rw [mul, transpose_mul]; rfl
lemma orthogonal [Fintype ι] [DecidableEq κ] (he : Function.Injective e) :
    (insertion e).transpose * insertion e = 1 := by
  rw [transpose_mul]; ext i j
  simp [insertion, Matrix.one_apply, he.eq_iff, eq_comm]
lemma dot_push [Fintype ι] [Fintype κ] (x : κ → ℝ) (y : ι → ℝ) :
    dotProduct (insertion e *ᵥ x) y = dotProduct x ((insertion e).transpose *ᵥ y) := by
  rw [dotProduct_transpose_mulVec, dotProduct_comm]
lemma dot_insert [Fintype ι] [Fintype κ] (he : Function.Injective e) (x y : κ → ℝ) :
    dotProduct (insertion e *ᵥ x) (insertion e *ᵥ y) = dotProduct x y := by
  classical
  rw [dot_push, mulVec_mulVec, orthogonal e he, one_mulVec]
lemma dot_compress [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ) (x y : κ → ℝ) :
    dotProduct (insertion e *ᵥ x) (A *ᵥ (insertion e *ᵥ y)) = dotProduct x ((A.submatrix e e) *ᵥ y) := by
  rw [dot_push, mulVec_mulVec, mulVec_mulVec, compress]
end insertion

variable [Fintype ι]

/-- Counting form gap (works with a total inverse operation; must separately
check positivity of the constant!). -/
structure Gap (A : Matrix ι ι ℝ) (r : ℝ) : Prop where
  lower (v : ι → ℝ) : r*dotProduct v v ≤ dotProduct v (A *ᵥ v)

lemma normSum_nn (v : ι → ℝ) : 0 ≤ dotProduct v v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
lemma le_normSum (v : ι → ℝ) (i : ι) : (v i)^2 ≤ dotProduct v v := by
  rw [sq]; exact Finset.single_le_sum (fun i _ => mul_self_nonneg _) (Finset.mem_univ i)

/-- Elementary Schur test of just a quadratic form. Symmetry not needed. -/
lemma schur_qf (D : Cost X) (a : ι → X) {A : Matrix ι ι ℝ} {M : ℝ} (h : D.Schur a a 0 M A) (x : ι → ℝ) :
    |dotProduct x (A *ᵥ x)| ≤ M * dotProduct x x := by
  let f (i j) := x i * (A i j * x j)
  let r (i j) := |A i j| * (x i * x i)
  let c (i j) := |A i j| * (x j * x j)
  have he (i j) : |f i j| ≤ r i j/2 + c i j/2 := by
    unfold f r c; rw [abs_mul,abs_mul]
    have hx := mul_nonneg (abs_nonneg (A i j)) (sq_nonneg (|x i| - |x j|))
    rw [sub_sq, sq_abs, sq_abs] at hx
    linarith only [hx]
  have hr : ∑ i, ∑ j, r i j/2 ≤ M * dotProduct x x /2 := by
    unfold r
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul, dotProduct, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
    exact mul_le_mul_of_nonneg_right (by simpa only [D.weight_zero,one_mul] using h.rows.bound i) (mul_self_nonneg _)
  have hc : ∑ i, ∑ j, c i j/2 ≤ M * dotProduct x x /2 := by
    rw [Finset.sum_comm]; unfold c
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul, dotProduct, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
    exact mul_le_mul_of_nonneg_right (by simpa only [Matrix.transpose_apply,D.weight_zero,one_mul] using h.cols.bound i) (mul_self_nonneg _)
  have H : |∑ i, ∑ j, f i j| ≤ _ := calc
    _ ≤ ∑ i, |∑ j, f i j| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ i, ∑ j, |f i j| := Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ i, ∑ j, (r i j / 2 + c i j / 2) := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j
    _ ≤ M * dotProduct x x := by simp_rw [Finset.sum_add_distrib]; linarith only [hr,hc]
  simpa only [dotProduct, mulVec, f, Finset.mul_sum] using H

namespace Gap
variable {A B : Matrix ι ι ℝ} {r t u : ℝ}
lemma mono (h : Gap A r) (he : t ≤ r) : Gap A t :=
  ⟨fun v => (mul_le_mul_of_nonneg_right he (normSum_nn _)).trans (h.lower v)⟩
lemma submatrix [Fintype κ] (e : κ → ι) (he : Function.Injective e) (h : Gap A r) :
    Gap (A.submatrix e e) r := by
  classical
  constructor; intro v
  simpa only [insertion.dot_compress, insertion.dot_insert e he] using h.lower (insertion e *ᵥ v)
lemma shift [DecidableEq ι] (h : Gap A r) (u : ℝ) : Gap (A + u • 1) (r+u) := by
  constructor; intro v
  simpa only [add_mul, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul, add_le_add_iff_right] using (h.lower v)

lemma perturb {D : Cost X} {a : ι → X} (h : Gap A r) (hb : D.Schur a a 0 t (B-A)) : Gap B (r-t) := by
  constructor; intro v
  have ht := (abs_le.mp (schur_qf D a hb v)).1
  rw [Matrix.sub_mulVec, dotProduct_sub] at ht
  linarith only [h.lower v, ht]
lemma trivial_null (h : Gap A r) (hr : 0 < r) {v : ι → ℝ} (hv : A *ᵥ v = 0) : v = 0 := by
  have ht := h.lower v
  rw [hv, dotProduct_zero] at ht
  funext i
  have hh := le_trans (mul_le_mul_of_nonneg_left (le_normSum v i) hr.le) ht
  change v i = 0
  by_contra H
  exact (not_lt_of_ge hh) (mul_pos hr (sq_pos_of_ne_zero H))
lemma isUnit [DecidableEq ι] (h : Gap A r) (hr : 0 < r) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y he
  exact sub_eq_zero.mp (h.trivial_null hr (by rw [mulVec_sub, sub_eq_zero]; exact he))
lemma unit_det [DecidableEq ι] (h : Gap A r) (hr : 0 < r) : IsUnit A.det :=
  (A.isUnit_iff_isUnit_det).mp (h.isUnit hr)

/-- Point bound via a unit input and the output of any right inverse. -/
lemma point [DecidableEq ι] (h : Gap A r) (hr : 0 < r) (ht : A * B = 1) (i j : ι) :
    |B i j| ≤ r⁻¹ := by
  let v := fun k => B k j
  have hv : A *ᵥ v = Pi.single j 1 := by
    funext k
    change (A*B) k j = _
    simp [ht, Matrix.one_apply, Pi.single_apply]
  have he := h.lower v
  rw [hv, dotProduct_single, mul_one] at he
  have hy := le_trans (mul_le_mul_of_nonneg_left (le_normSum v j) hr.le) he
  have H : v j ≤ r⁻¹ := by
    by_cases h : 0 < v j
    · apply le_of_mul_le_mul_left (a := r*v j) ?_ (mul_pos hr h)
      calc _ = r * (v j)^2 := by ring
           _ ≤ v j := hy
           _ = _ := by field_simp
    exact le_trans (le_of_not_gt h) (inv_pos.mpr hr).le
  have hx := le_trans (mul_le_mul_of_nonneg_left (le_normSum v i) hr.le) (he.trans H)
  have hh : (v i)^2 ≤ (r⁻¹)^2 := by
    apply le_of_mul_le_mul_left (a := r) ?_ hr
    refine hx.trans_eq ?_; field_simp
  change |v i| ≤ r⁻¹
  rw [abs_le]; constructor <;> nlinarith only [hh, inv_pos.mpr hr]
end Gap
end YM.FreeResolvent
