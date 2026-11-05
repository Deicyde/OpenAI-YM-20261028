import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import YM.Further.CURVED_GAUSSIAN_JETS.Algebra
import YM.Next.BOUNDARY.Coordinates
import YM.Next.SCHEDULE.Blocks


/-!
# Projections/independence after the conditional measure change

Each served expectation under the SAME centered law on its Z inputs,
not iid per tag use. The hypothesis of cross zero reflects the actual
covariance kernel range and orientation per sector. Includes conditional
residual variable law as a product in physical linear charts, and is
usable even with derivative multi-reads at the SAME positions. No
factorization across variables indexing which law this is itself.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Law
open Function Filter MeasureTheory Set Matrix ProbabilityTheory
open scoped Topology BigOperators Classical RealInnerProductSpace
variable {I J K X : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J] [DecidableEq K]

abbrev Chart (I : Type*) := EuclideanSpace ℝ I

def field (A : Matrix J I ℝ) : Chart I →L[ℝ] Chart J := (Matrix.toEuclideanLin A).toContinuousLinearMap
lemma field_works (A : Matrix J I ℝ) (x : Chart I) : field A x=WithLp.toLp 2 (A *ᵥ x.ofLp) := rfl
lemma trans (A : Matrix J I ℝ) (x : Chart I) (y : Chart J) : inner ℝ x (field A.transpose y)=inner ℝ (field A x) y := by
  simp only [field_works, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Matrix.mulVec_transpose, dotProduct_mulVec]

def slice (A : Matrix J I ℝ) (C : Table I) := A*C*A.transpose
lemma slice_value (A : Matrix J I ℝ) (C : Table I) (x y : Chart J) : dotProduct (field A.transpose x).ofLp (C*ᵥ(field A.transpose y).ofLp)=dotProduct x.ofLp ((slice A C)*ᵥy.ofLp) := by
  unfold slice; rw [← mulVec_mulVec,← mulVec_mulVec, dotProduct_mulVec _ A, field_works, WithLp.ofLp_toLp, Matrix.mulVec_transpose]; rfl
lemma slice_semi (A : Matrix J I ℝ) {C : Table I} (h : C.PosSemidef) : (slice A C).PosSemidef := h.mul_mul_conjTranspose_same _

theorem observes (A : Matrix J I ℝ) {C : Table I} (h : C.PosSemidef) : MeasurePreserving (field A) (law C) (law (slice A C)) where
  measurable := by fun_prop
  map_eq := by
    haveI : IsProbabilityMeasure ((law C).map (field A)) := Measure.isProbabilityMeasure_map (by fun_prop)
    apply Measure.ext_of_charFun; funext t
    have he : charFun (Measure.map (field A) (law C)) t = charFun (law C) (field A.transpose t) := by
      simp_rw [charFun_apply, trans]
      rw [integral_map (by fun_prop) (by fun_prop)]
    rw [he, charFun_multivariateGaussian h, charFun_multivariateGaussian (slice_semi A h), slice_value,inner_zero_right, inner_zero_right]

theorem cross (A : Matrix J I ℝ) (B : Matrix K I ℝ) {C : Table I} (h : C.PosSemidef) (x : Chart J) (y : Chart K) :
    covariance (fun z=> inner ℝ x (field A z)) (fun z=> inner ℝ y (field B z)) (law C) = dotProduct x.ofLp ((A*C*B.transpose)*ᵥ y.ofLp) := by
  simp_rw [real_inner_comm _ x,real_inner_comm _ y,← trans,real_inner_comm (field A.transpose x),real_inner_comm (field B.transpose y),← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_multivariateGaussian h, ←mulVec_mulVec, Matrix.dotProduct_mulVec x.ofLp A, ←mulVec_transpose]
  rfl


theorem split (A : Matrix J I ℝ) (B : Matrix K I ℝ) {C : Table I} (h : C.PosSemidef) (hs : A*C*B.transpose=0) :
    IndepFun (field A) (field B) (law C) ∧ MeasurePreserving (fun z => (field A z, field B z)) (law C)
      ((law (slice A C)).prod (law (slice B C))) := by
  have ht : HasGaussianLaw (fun z => (field A z, field B z)) (law C) := IsGaussian.hasGaussianLaw_id.map ((field A).prod (field B))
  have he := ht.indepFun_of_covariance_inner fun x y => (cross A B h x y).trans (by rw [hs,zero_mulVec,dotProduct_zero])
  exact ⟨he,⟨by fun_prop, by rw [IndepFun.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop) he, (observes A h).map_eq,(observes B h).map_eq]⟩⟩




end YM.Further.CurvedGaussianJets.Law
