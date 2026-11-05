import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Pressure.Seeds
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian
import YM.Work.A05.Read
import YM.Work.A15


/-!
# Switching between two real positive Gaussian tables

Use the actual normalizations of  and SectorChange. Include also
possibly different translations (mu0 from ORDERED column convention).
When using C,m first then C',m', a stays = m+g Z = m'+g Z', thus OLD
z = new z + (m'-m)/g. Never drop the determinant or quadratic force.
Filter withDensity / section version: works also for signed or complex
observables/test words (once jointly measurable for the product version).
Positivity hypotheses essential. Compounded tags can sit in Y. Inactive
positions not part of g price.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Next SectorChange Matrix Gaussian MeasureTheory Function Set Filter
open scoped Classical ENNReal BigOperators

namespace Density
variable {ι Y X : Type*} {n : Type} [Fintype n] [DecidableEq n]
variable (A C : Gaussian.Table n)

/-- Remaining quadratic/additive correction when changing from A
covariance to C covariance, evaluating old variables at z+b. -/
def spice (b z : Gaussian.Vec n) := force C z/2 - force A (z+b)/2

/-- Pay `sqrt(det C/det A)`: this is for exchange of MEASURES;
the chart *unnormalized* factor paid outside `Licenses` has its own
determinant. -/
def chip := Real.sqrt C.det / Real.sqrt A.det

def replace (b z : Gaussian.Vec n) := chip A C * Real.exp (spice A C b z)

lemma chip_coat : chip A C = coat C / coat A := by
  unfold coat chip; rw [mul_div_mul_left _ _ (show dome n ≠ 0 from Gaussian.dome_pos.ne')]
lemma chip_income (hA : A.PosDef) (hC : C.PosDef) :
    chip A C = Real.exp ((1/2:ℝ) * Real.log (C.det/A.det)) := by
  unfold chip; rw [← Real.sqrt_div hC.det_pos.le]
  have he := div_pos hC.det_pos hA.det_pos
  have hh : Real.log (C.det/A.det) = Real.log ((Real.sqrt (C.det/A.det))^2) := by rw [Real.sq_sqrt he.le]
  rw [hh,Real.log_pow, ← mul_assoc]
  norm_num [Real.exp_log (Real.sqrt_pos.mpr he)]
lemma chip_pos (hA : A.PosDef) (hC : C.PosDef) : 0 < chip A C := div_pos (Real.sqrt_pos.mpr hC.det_pos) (Real.sqrt_pos.mpr hA.det_pos)
lemma replace_pos (hA : A.PosDef) (hC : C.PosDef) (b z : Gaussian.Vec n) : 0 < replace A C b z := mul_pos (chip_pos _ _ hA hC) (Real.exp_pos _)
lemma replace_cocycle (B : Gaussian.Table n) (hC : C.PosDef) (b c z : Gaussian.Vec n) :
    replace A C b (z+c) * replace C B c z = replace A B (b+c) z := by
  unfold replace chip spice; rw [show z+(b+c) = z+c+b from (by abel)]
  rw [mul_mul_mul_comm,← Real.exp_add,sub_add_sub_cancel']
  congr 1; field_simp [show Real.sqrt C.det ≠ 0 from (Real.sqrt_pos.mpr hC.det_pos).ne']
lemma replace_income (hA : A.PosDef) (hC : C.PosDef) (b z : Gaussian.Vec n) :
    Real.log (replace A C b z) = (1/2:ℝ)*Real.log (C.det/A.det)+spice A C b z := by
  unfold replace; rw [chip_income A C hA hC,← Real.exp_add,Real.log_exp]

lemma replace_on (b : Gaussian.Vec n) : Measurable (replace A C b) := by unfold replace spice force dotProduct mulVec; fun_prop

/-!
The real identity on normalized clouds. Measures completely specified
(cloud_formula); prove directly for any test or local factor with L¹ at
either price. No extra tags picked when evaluating this function.
-/
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

def priced (b : Gaussian.Vec n) (F : Gaussian.Vec n → X) (z : Gaussian.Vec n) : X := replace A C b z • F (z+b)

private lemma cloud_l1 {A : Gaussian.Table n} (h : A.PosDef) (f : Gaussian.Vec n → X) :
    Integrable f (cloud A) ↔ Integrable (fun z => ratio A z • f z) := by
  rw [cloud_formula h,integrable_withDensity_iff_integrable_smul' (measurable_ratio _).ennreal_ofReal (Filter.Eventually.of_forall fun i => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (ratio_pos h _).le]

private lemma cloud_integral {A : Gaussian.Table n} (h : A.PosDef) (f : Gaussian.Vec n → X) :
    (∫ z, f z ∂cloud A) = ∫ z, ratio A z • f z := by
  rw [cloud_formula h,integral_withDensity_eq_integral_toReal_smul (measurable_ratio _).ennreal_ofReal (Filter.Eventually.of_forall fun i => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (ratio_pos h _).le]

lemma ratio_switch (hC : C.PosDef) (b z : Gaussian.Vec n) :
    ratio C z * replace A C b z=ratio A (z+b) := by
  unfold ratio replace spice; rw [chip_coat]
  rw [mul_mul_mul_comm,← Real.exp_add,show -(force C z)/2+(force C z/2-force A (z+b)/2)=-(force A (z+b))/2 by ring,
    div_eq_mul_inv, ← mul_assoc (coat C)⁻¹, inv_mul_cancel₀ (coat_pos hC).ne',one_mul]

theorem exchange (hA : A.PosDef) (hC : C.PosDef) (b : Gaussian.Vec n) (F : Gaussian.Vec n → X) :
    (Integrable F (cloud A) ↔ Integrable (priced A C b F) (cloud C)) ∧
      (∫ z, F z ∂cloud A)=(∫ z, priced A C b F z ∂cloud C) := by
  let U : Gaussian.Vec n ≃ᵐ Gaussian.Vec n := MeasurableEquiv.addRight b
  let μ : Measure (Gaussian.Vec n) := volume
  have he : MeasurePreserving U μ μ := measurePreserving_add_right ..
  let f z := ratio A z • F z
  have hi : (fun z => ratio C z • priced A C b F z)=f ∘ U := funext fun z => (smul_smul ..).trans (by rw [ratio_switch A C hC]; rfl)
  rw [cloud_l1 hA, cloud_l1 hC,cloud_integral hA,cloud_integral hC,hi]
  exact ⟨(he.integrable_comp_emb U.measurableEmbedding).symm, (he.integral_comp' f).symm⟩


end Density
end YM.AnalyticBridge.LocalGaussianLaws
