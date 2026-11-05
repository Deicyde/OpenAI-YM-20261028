import YM.MultiNext.VACUUM_STABILITY.Gaussian.Laplace
import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Price


/-!
# Quadratic Laplace prices for the genuine cloud

Adapter from counting covariance budget to the accepted `Gauss.conditional`.
This also lets us purchase lower bounds on actual Gaussian normalizers in
terms of trace of a diagonal *weight*, not paying for volume or presuming
determinant cancellation. All finite, no assertions about infinite-volume
limits.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianInsertion

open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
open Multi.Vacuum (Gauss.pay Gauss.conditional Gauss.standard Gauss.mapRows Gauss.adjBound Gauss.squares)
open scoped Topology BigOperators Classical ENNReal MatrixOrder

variable {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J]
  {A : Gaussian.Table ι} {w z : Vec ι} {K : ℝ}

omit [DecidableEq ι] in
lemma matrix_generator {B : Matrix ι J ℝ} (h : Ceiling (B * B.transpose) K) :
    Gauss.adjBound (fun i j => B i j) K := by
  intro u
  have he : ∀ {ι : Type} [Fintype ι] (v : Vec ι), Gauss.squares v = v ⬝ᵥ v := by
    intro ι hι v
    simp only [Gauss.squares, dotProduct, sq]
  rw [he, he]
  change (B.transpose *ᵥ u) ⬝ᵥ (B.transpose *ᵥ u) ≤ _
  rw [dotProduct_transpose_mulVec, mulVec_mulVec]
  exact h u

lemma from_standard (A : Gaussian.Table ι) :
    MeasurePreserving (fun x => CFC.sqrt A *ᵥ x) (Gauss.standard ι) (cloud A) :=
  ⟨acts_meas (CFC.sqrt A), paid A⟩

lemma root_gram (hA : A.PosSemidef) : CFC.sqrt A * (CFC.sqrt A).transpose = A := by
  have hu := isHermitian_iff_isSymm.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  rw [hu.eq, CFC.sqrt_mul_sqrt_self A hA.nonneg]

/-- Uniform because it pays for the diagonal trace, not per row
irrespective of weight. -/
theorem cloud_laplace (hA : A.PosSemidef) (hK : Ceiling A K) (hp : 0 ≤ K)
    (hw : ∀ i, 0 ≤ w i) (he : ∀ i, K*w i ≤ 1/4) :
    Integrable (fun z => Real.exp (Gauss.pay w z)) (cloud A) ∧
      (∫ z, Real.exp (Gauss.pay w z) ∂cloud A) ≤ Real.exp (2*K*∑ i, w i) := by
  have h := from_standard A
  have hh : Ceiling (CFC.sqrt A * (CFC.sqrt A).transpose) K := (root_gram hA).symm ▸ hK
  obtain ⟨hf,hb⟩ := Gauss.conditional _ _ (matrix_generator hh) hp w hw he
  let F z := Real.exp (Gauss.pay w z)
  have hm : Measurable F := by unfold F Gauss.pay; fun_prop
  have hu : Integrable F (cloud A) := (h.integrable_comp hm.aestronglyMeasurable).mp hf
  refine ⟨hu,?_⟩
  rw [← h.map_eq, integral_map h.aemeasurable hm.aestronglyMeasurable]
  refine hb.trans_eq ?_
  rw [Finset.mul_sum]
  simp_rw [mul_assoc]

/-- Bounding an observable exponential under any (possibly shifted) real
Gaussian with uniform covariance ceiling. `b` includes any cost of
recentering. -/
lemma laplace_price (hA : A.PosSemidef) (hK : Ceiling A K) (hp : 0 ≤ K)
    (hw : ∀ i, 0 ≤ w i) (he : ∀ i, K*w i ≤ 1/4) {F : Vec ι → ℝ}
    (hm : Measurable F) (m : Vec ι) {b : ℝ} (hl : ∀ z, F (m+z) ≤ b + Gauss.pay w z) :
    Integrable (fun x => Real.exp (F x)) (law A m) ∧
      (∫ x, Real.exp (F x) ∂law A m) ≤ Real.exp (b+2*K*∑ i, w i) := by
  obtain ⟨h1,h2⟩ := cloud_laplace hA hK hp hw he
  have hh z : Real.exp (F (m+z)) ≤ Real.exp b * Real.exp (Gauss.pay w z) := by
    rw [← Real.exp_add]; exact Real.exp_monotone (hl z)
  have hu : Integrable (fun z => Real.exp (F (m+z))) (cloud A) := (h1.const_mul _).mono'
    (Real.continuous_exp.measurable.comp (hm.comp (measurable_const.add measurable_id))).aestronglyMeasurable <|
    Eventually.of_forall fun z => (Real.norm_of_nonneg (Real.exp_pos _).le).trans_le (hh z)
  refine ⟨(integrable_law A m _).mpr hu,?_⟩
  rw [integral_law A m (fun x => Real.exp (F x)), Real.exp_add]
  refine (integral_mono hu (h1.const_mul (Real.exp b)) hh).trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

omit [DecidableEq ι] in
lemma pay_add_le (hw : ∀ i, 0 ≤ w i) (z y : Vec ι) :
    Gauss.pay w (y + z) ≤ 2 * Gauss.pay w y + 2 * Gauss.pay w z := by
  unfold Gauss.pay
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Pi.add_apply]
  nlinarith only [mul_nonneg (hw i) (sq_nonneg (y i - z i))]

omit [DecidableEq ι] in
lemma pay_scale (r : ℝ) (z : Vec ι) : Gauss.pay (r • w) z = r * Gauss.pay w z := by
  unfold Gauss.pay
  simp [Finset.mul_sum, mul_assoc]

end YM.SectorTools.PhysicalGaussianInsertion
