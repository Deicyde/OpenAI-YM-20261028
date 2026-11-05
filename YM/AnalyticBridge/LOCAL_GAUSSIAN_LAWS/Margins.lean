import YM.Next.EXTRACTION.Tails
import YM.Push.FREE_RESOLVENT.Windows
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian
import YM.Work.B06

/-!
# Reindex and restrict the SAME Gaussian

Rectangular pushforwards, singular covariance allowed (but don't then
apply Density.exchange). Law/probability interpretation of local
replacement, and proves permission to use reindexing even between
orthogonally related windows. A projection L to local coordinates does
NOT replace a pane by a local recomputation: the covariance of those
coordinates is L * THE SAME full C * L^T.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set MeasureTheory ProbabilityTheory Matrix WithLp Next SectorChange SectorChange.Gaussian
open scoped Topology ENNReal Classical BigOperators InnerProductSpace

namespace Density
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def skim (L : Matrix m n ℝ) (Q : Gaussian.Table n) := L * Q * L.transpose

lemma skim_positive {Q : Gaussian.Table n} (h : Q.PosSemidef) (L : Matrix m n ℝ) : (skim L Q).PosSemidef := by
  have he := h.conjTranspose_mul_mul_same L.transpose
  rwa [show L.transpose.conjTranspose=L from rfl] at he

-- direct dual computation
def tool (L : Matrix m n ℝ) (x : EuclideanSpace ℝ n) : EuclideanSpace ℝ m := toLp 2 (L*ᵥ ofLp x)

private lemma ctool (L : Matrix m n ℝ) : Continuous (tool L) := by
  unfold tool
  refine (PiLp.continuous_toLp 2 _).comp ?_
  simp_rw [← Matrix.toLin'_apply]
  exact (Matrix.toLin' L).continuous_on_pi.comp (PiLp.continuous_ofLp 2 _)

private lemma transpose_cost (L : Matrix m n ℝ) (x : EuclideanSpace ℝ n) (y : EuclideanSpace ℝ m) :
    inner ℝ (tool L x) y = inner ℝ x (tool L.transpose y) := by
  have he {n : Type} [Fintype n] (x y : EuclideanSpace ℝ n) : inner ℝ x y = ofLp y ⬝ᵥ ofLp x := by rw [PiLp.inner_apply]; rfl
  rw [he,he,tool,tool]
  change ((ofLp y) ⬝ᵥ (L *ᵥ ofLp x)) = ((L.transpose *ᵥ ofLp y) ⬝ᵥ ofLp x)
  rw [← Matrix.dotProduct_transpose_mulVec,dotProduct_comm]


/-- Arbitrary joint linear read of a Gaussian.cloud. Use even for zeroing
inactive coordinates or overlapping insertions. -/
theorem gathered {Q : Gaussian.Table n} (h : Q.PosSemidef) (L : Matrix m n ℝ) :
    MeasurePreserving (L *ᵥ ·) (cloud Q) (cloud (skim L Q)) := by
  let θ := multivariateGaussian 0 Q
  have hi : Continuous (L *ᵥ ·) := by simp_rw [← Matrix.toLin'_apply]; exact (Matrix.toLin' L).continuous_on_pi
  have hm := (ctool L).measurable
  constructor
  · exact hi.measurable
  rw [cloud,Measure.map_map hi.measurable (PiLp.continuous_ofLp 2 _).measurable,show (L *ᵥ ·) ∘ ofLp=ofLp ∘ tool L from rfl,
    ← Measure.map_map (PiLp.continuous_ofLp 2 _).measurable hm,cloud]
  apply congr_arg (Measure.map (ofLp : EuclideanSpace ℝ m → _))
  letI : IsProbabilityMeasure (θ.map (tool L)) := Measure.isProbabilityMeasure_map hm.aemeasurable
  apply Measure.ext_of_charFun
  funext y
  have he : charFun (θ.map (tool L)) y=charFun θ (tool L.transpose y) := by
    unfold charFun
    rw [integral_map hm.aemeasurable (by fun_prop)]
    simp_rw [transpose_cost]
  rw [he,charFun_multivariateGaussian h,charFun_multivariateGaussian (skim_positive h L)]
  simp only [inner_zero_right,Complex.ofReal_zero,zero_mul]
  rw [skim,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  let v := ofLp y; let a := L.transpose *ᵥ v
  have hh : a ⬝ᵥ (Q *ᵥ a)=v ⬝ᵥ (L *ᵥ (Q *ᵥ a)) := by
    rw [dotProduct_comm a]; change ((Q *ᵥ a) ⬝ᵥ (L.transpose *ᵥ v))=_; rw [Matrix.dotProduct_transpose_mulVec]
  change Complex.exp (0-(↑(a ⬝ᵥ (Q *ᵥ a)):ℂ)/2) = Complex.exp (0-(↑(v ⬝ᵥ (L *ᵥ (Q *ᵥ a))):ℂ)/2)
  rw [hh]

/-- In particular actual *subarray*, independent of numbering. -/
lemma sample (r : m ↪ n) {Q : Gaussian.Table n} (h : Q.PosSemidef) :
    MeasurePreserving (fun x : SectorChange.Gaussian.Vec n => x ∘ r) (cloud Q) (cloud (Q.submatrix r r)) := by
  let L := (FreeResolvent.insertion r).transpose
  have H := gathered h L
  rw [show skim L Q=Q.submatrix r r from FreeResolvent.insertion.compress ..] at H
  rwa [show (fun x => x ∘ r)=fun x=> L *ᵥ x from funext fun x => funext fun i => (FreeResolvent.probe_insert r x i).symm]



end Density
end YM.AnalyticBridge.LocalGaussianLaws
