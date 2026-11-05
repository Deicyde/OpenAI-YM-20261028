import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07


/-!
# Scalar operators, counting (not sup)
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate InnerProductSpace
section metric
variable {ι n : Type*} [Fintype ι] [Fintype n] {K : Type*} [RCLike K]

/-- Counting l² for all row/column/field bounds below. -/
def ell2 (x : ι→K) := ‖WithLp.toLp 2 x‖
lemma ell_nonneg (x : ι→K) : 0 ≤ ell2 x := norm_nonneg _
@[simp] lemma ell_zero : ell2 (0:ι→K)=0 := norm_zero
@[simp] lemma ell_neg (x : ι→K) : ell2 (-x)=ell2 x := norm_neg _
lemma ell_tri (x y : ι→K) : ell2 (x+y) ≤ ell2 x+ell2 y := norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)
lemma ell_sub (x y : ι→K) : ell2 (x-y) ≤ ell2 x+ell2 y := norm_sub_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)
lemma ell_smul (a : K) (x : ι→K) : ell2 (a • x) = ‖a‖*ell2 x := norm_smul a (WithLp.toLp 2 x)
lemma ell_pos {x : ι→K} : 0 < ell2 x ↔ x≠0 := by
  rw [ell2, norm_pos_iff]; exact not_congr (WithLp.toLp_injective 2).eq_iff
lemma square_length (x : ι→K) : ell2 x ^ 2 = ∑ i, ‖x i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _

lemma real_area (x y : ι→ℝ) : inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = dotProduct x y := by
  rw [real_inner_comm]; simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial]; rfl
lemma complex_area (x y : ι→ℂ) : inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y)=dotProduct (star x) y := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,dotProduct, Pi.star_apply, starRingEnd_apply]
  simp only [mul_comm]
lemma real_count (x : ι→ℝ) : dotProduct x x = ell2 x ^ 2 := by rw [← real_area, real_inner_self_eq_norm_sq]; rfl
lemma complex_count (x : ι→ℂ) : dotProduct (star x) x = ((ell2 x^2:ℝ):ℂ) := by rw [← complex_area, inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]; rfl
lemma norm_real_area (x y : ι→ℝ) : |dotProduct x y| ≤ ell2 x*ell2 y := by rw [← real_area]; exact abs_real_inner_le_norm ..
lemma norm_area (x y : ι→ℂ) : ‖dotProduct (star x) y‖ ≤ ell2 x*ell2 y := by rw [← complex_area]; exact norm_inner_le_norm ..
lemma adjoint_area (A : Matrix ι n ℂ) (x : n→ℂ) (y : ι→ℂ) :
    dotProduct (star (A *ᵥ x)) y=dotProduct (star x) (Aᴴ *ᵥ y) := by rw [Matrix.star_mulVec, dotProduct_mulVec]


section schur
variable {A : Matrix ι n K} {a b C : ℝ}
omit [Fintype ι] in
lemma rowprice (x : n→K) (i : ι) : ‖(A*ᵥ x) i‖^2 ≤ (∑ j,‖A i j‖)*∑ j, ‖A i j‖*‖x j‖^2 := by
  let f (j) := Real.sqrt ‖A i j‖
  have hh : ‖(A*ᵥ x) i‖ ≤ ∑ j : n,f j*(f j*‖x j‖) := by
    apply (norm_sum_le ..).trans_eq
    apply Finset.sum_congr rfl; intro j _; rw [norm_mul,← mul_assoc,← pow_two,show f _ ^ 2=_ from Real.sq_sqrt (norm_nonneg _)]
  apply (pow_le_pow_left₀ (norm_nonneg _) hh _).trans
  convert! (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (fun j => f j*‖x j‖)) using 1
  simp only [f, mul_pow,Real.sq_sqrt (norm_nonneg _)]
lemma smear (h : ∀ i, ∑ j, ‖A i j‖ ≤ a) (ha : 0 ≤ a) (g : ∀ j, ∑ i, ‖A i j‖ ≤ b)
    (H : a*b ≤ C^2) (hc : 0 ≤ C) (x : n→K) : ell2 (A *ᵥ x) ≤ C*ell2 x := by
  apply (sq_le_sq₀ (ell_nonneg _) (mul_nonneg hc (ell_nonneg _))).mp
  rw [square_length, mul_pow,square_length]
  apply le_trans _ (mul_le_mul_of_nonneg_right H (Finset.sum_nonneg fun i _ => sq_nonneg _))
  calc
    _ ≤ ∑ i : ι, a * ∑ j : n, ‖A i j‖ * ‖x j‖^2 := Finset.sum_le_sum fun i _ => (rowprice x i).trans (mul_le_mul_of_nonneg_right (h i) (by positivity))
    _ ≤ _ := by
      rw [← Finset.mul_sum,Finset.sum_comm,mul_assoc,Finset.mul_sum _ _ b]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => by
        rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (g i) (sq_nonneg _)) ha
end schur

def offer (x : ι→ℝ) := fun i => (x i:ℂ)
lemma offer_ell (x : ι→ℝ) : ell2 (offer x)=ell2 x := by
  have he : ell2 (offer x)^2=ell2 x^2 := by rw [square_length,square_length]; simp only [offer, Complex.norm_real]
  nlinarith [ell_nonneg x,ell_nonneg (offer x)]
omit [Fintype ι] in
lemma offer_mat (A : Matrix ι n ℝ) (x : n→ℝ) : offer (A*ᵥ x)=approached A *ᵥ offer x := by
  funext i; simp only [offer,approached,mulVec,dotProduct, Complex.ofReal_sum,Complex.ofReal_mul]; rfl
omit [Fintype ι] [Fintype n] in
lemma approach_H (A : Matrix ι n ℝ) : approached A.transpose=(approached A)ᴴ := by ext i j; simp [approached]
end metric
end YM.AnalyticNext.QuarticMatch.Hessian
