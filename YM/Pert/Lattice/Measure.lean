import YM.Pert.Lattice.Action
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian
/-! An actual, finite-dimensional Gaussian probability for the top graph generator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Orb
open Lattice Filter Matrix MeasureTheory ProbabilityTheory Next.SectorChange.Gaussian
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators ENNReal
variable {G : Gauge} {n : Side}
abbrev GIx (G : Gauge) (n : Side) := Fin (Module.finrank ℝ (Potential G n))
abbrev Coords (G : Gauge) (n : Side) := GIx G n → ℝ
def expand (G : Gauge) (n : Side) : Coords G n ≃ₗ[ℝ] Potential G n := (Module.finBasis ℝ (Potential G n)).equivFun.symm
def seed (i : GIx G n) : Potential G n := Module.finBasis ℝ _ i
lemma expand_eq (x : Coords G n) : expand G n x = ∑ i, x i • seed i := Module.Basis.equivFun_symm_apply ..

def precision (G : Gauge) (n : Side) : Table (GIx G n) := .of (fun i j => form (seed i) (seed j))
lemma scalar_formula (x y : Coords G n) : x ⬝ᵥ ((precision G n) *ᵥ y) = form (expand G n x) (expand G n y) := by
  rw [expand_eq,expand_eq]
  change _ = formL G n _ _; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]
  change ∑ i, x i * (∑ j, formL G n (seed i) (seed j) * y j) = _
  simp_rw [Finset.mul_sum,smul_eq_mul]; rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)); ring
lemma precision_pos (G : Gauge) (n : Side) : (precision G n).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]; refine ⟨IsHermitian.ext fun i j => ?_, fun x hx => ?_⟩
  · exact form_symm ..
  rw [star_trivial,scalar_formula]; exact form_pos (fun e => hx ((expand G n).injective (e.trans (map_zero (expand G n)).symm)))
def covarianceM (G : Gauge) (n : Side) := (precision G n)⁻¹
lemma covarianceM_pos (G : Gauge) (n : Side) : (covarianceM G n).PosDef := (precision_pos G n).inv
lemma scalar_inverse (x : Coords G n) : force (covarianceM G n) x = form (expand G n x) (expand G n x) := by
  unfold force covarianceM; rw [nonsing_inv_nonsing_inv,scalar_formula]; exact Matrix.isUnit_iff_isUnit_det _ |>.1 (precision_pos G n).isUnit

def data (G : Gauge) (n : Side) := cloud (covarianceM G n)
lemma isLaw : IsGaussian (data G n) := by
  unfold data cloud
  let L : EuclideanSpace ℝ (GIx G n) →L[ℝ] Coords G n := (WithLp.linearEquiv 2 ℝ _).toContinuousLinearMap
  exact inferInstanceAs (IsGaussian ((multivariateGaussian 0 (covarianceM G n)).map L))
instance : IsProbabilityMeasure (data G n) := inferInstanceAs (IsProbabilityMeasure (cloud _))
lemma densityFormula : data G n = volume.withDensity (fun x : Coords G n => ENNReal.ofReal ((coat (covarianceM G n))⁻¹ * Real.exp (-(form (expand G n x) (expand G n x)) / 2))) := by
  simpa only [data,ratio,←scalar_inverse] using (cloud_formula (covarianceM_pos G n))
lemma mean_formula (i : GIx G n) : (∫ v : Coords G n, v i ∂data G n) = 0 := cloud_center _ _
lemma cov_formula (i j : GIx G n) : ProbabilityTheory.covariance (fun v : Coords G n => v i) (fun v => v j) (data G n) = covarianceM G n i j := cloud_cov _ (covarianceM_pos G n) i j
lemma moment_integrable (k : ℕ) : Integrable (fun v : Coords G n => (1 + ‖v‖)^k) (data G n) := by
  haveI := isLaw (G:=G) (n:=n)
  by_cases hk : k=0
  · simp [hk]
  have hk' := ((IsGaussian.memLp_id (data G n) (k:ℝ≥0∞) (by simp)).norm.add (memLp_const (1:ℝ))).integrable_norm_pow hk
  convert! hk' using 2
  simp only [Pi.add_apply, id_eq, Real.norm_eq_abs]; rw [abs_of_nonneg (by positivity), add_comm]
end YM.Pert.Orb
