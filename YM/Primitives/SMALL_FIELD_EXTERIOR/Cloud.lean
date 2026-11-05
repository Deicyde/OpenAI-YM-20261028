import Mathlib.MeasureTheory.Measure.Tilted
import YM.Primitives.SMALL_FIELD_EXTERIOR.Perturb
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian



/-!
# Normalized response with respect to the actual `SectorChange.Gaussian.cloud`

Positive definite native covariance, real tilt, compact sup cube with
all coordinates. Don't mix this box conditioning with claims about
fields under other guards.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter MeasureTheory Matrix
open YM.Next.SectorChange YM.Next.SectorChange.Gaussian
open scoped Topology BigOperators ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι] {W f g : Points ι → ℝ} {r x M m : ℝ} {C : Matrix ι ι ℝ}

def stiffness (C : Matrix ι ι ℝ) := fun y : Points ι => Gaussian.force C y/2

def load (C : Matrix ι ι ℝ) (W : Points ι → ℝ) := stiffness C + W

lemma stiffness_diff (C : Matrix ι ι ℝ) : ContDiff ℝ ω (stiffness C) := by
  unfold stiffness force mulVec dotProduct; fun_prop


def cloudy (C : Matrix ι ι ℝ) (r : ℝ) := (cloud C).restrict (cube ι r)
def plume (C : Matrix ι ι ℝ) (r : ℝ) (W : Points ι → ℝ) := (cloudy C r).tilted (-W)

/-- Exact weight price, BEFORE any approximation. -/
lemma forms (hC : C.PosDef) (W f : Points ι → ℝ) (r : ℝ) :
    (∫ y, Real.exp (-W y)*f y ∂(cloudy C r))=(Gaussian.coat C)⁻¹ * raw r (load C W) f := by
  have ht (y : Points ι) : (ENNReal.ofReal (ratio C y)).toReal * (Real.exp (-W y)*f y) =
      (Gaussian.coat C)⁻¹ * (Real.exp (-(load C W y))*f y) := by
    rw [ENNReal.toReal_ofReal (ratio_pos hC y).le, ratio, load,Pi.add_apply,neg_add, Real.exp_add]
    unfold stiffness; rw [neg_div]; ring
  unfold cloudy; rw [cloud_formula hC, setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_ratio _ |>.ennreal_ofReal)
    (Eventually.of_forall fun _ => by simp) _ (cube_meas _)]
  simp_rw [smul_eq_mul,ht,integral_const_mul]; rfl



lemma plume_read (hC : C.PosDef) (W f : Points ι → ℝ) (r : ℝ) :
    (∫ y,f y ∂plume C r W) = mean r (load C W) f := by
  have ht := forms hC W 1 r
  simp only [Pi.one_apply,mul_one] at ht
  unfold plume; rw [integral_tilted]; simp only [smul_eq_mul,Pi.neg_apply,div_mul_eq_mul_div,integral_div, ht, forms hC]
  unfold mean; rw [mul_div_mul_left _ _ (inv_pos.mpr (coat_pos hC)).ne']



def correlated (μ : Measure (Points ι)) (f g : Points ι → ℝ) :=
    (∫ y, f y*g y ∂μ) - (∫ y, f y ∂μ)*(∫ y,g y ∂μ)


lemma covariance_cloud (hC : C.PosDef) : correlated (plume C r W) f g=covariance r (load C W) f g := by
  unfold covariance correlated; rw [← plume_read hC W (f*g), plume_read hC W f, plume_read hC W g]; rfl







/-- Inserting a source with POSITIVE exponential sign. -/
theorem plume_source (hC : C.PosDef) (hr : 0 < r) (hW : ContinuousOn W (cube ι r)) (hf : ContinuousOn f (cube ι r))
    (hg : ContinuousOn g (cube ι r)) (x : ℝ) :
    HasDerivAt (fun t => ∫ y,g y ∂plume C r (W-t • f)) (correlated (plume C r (W-x • f)) f g) x := by
  have he (t : ℝ) : load C (W-t • f)=load C W-t • f := by unfold load; abel
  have H := (stiffness_diff C).continuous
  simp_rw [covariance_cloud hC, plume_read hC, he]
  exact source (H.continuousOn.add hW) hf hg hr x
end YM.Primitives.SmallFieldExterior
