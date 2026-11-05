import YM.Analysis.Polydisc
import YM.Pressure.Seeds
import YM.Push.FREE_RESOLVENT.Gap
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian


/-!
# One local Gaussian marginal and its prices for ALL the tests

Quantitative gap on the **precision of the marginal**, not the entry
of a projection of the inverse. Adaptors from exponential-Schur or
quadratic pricing in B70. Thus no choice of new per-atom Gaussians.
Also with a proper sublist of frozen Haar variables.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice Wilson RG Next.SectorChange Next.SectorChange.Gaussian
open MeasureTheory ProbabilityTheory WithLp Matrix
open scoped Topology BigOperators RealInnerProductSpace MatrixOrder

variable {ι κ : Type} [Fintype ι] [Fintype κ]

section volume

private def look (a : κ → ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ := LinearMap.toContinuousLinearMap
  { toFun x := toLp 2 (fun i => x (a i))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable [DecidableEq ι] [DecidableEq κ] {C : Next.SectorChange.Gaussian.Table ι}
-- look_law adapts the Gaussian coordinate marginal proof from Mathlib's measurePreserving_restrict₂_multivariateGaussian (Rémy Degenne and Etienne Marion). Copyright (c) 2026 Rémy Degenne. All rights reserved. Apache-2.0. See NOTICE.
private lemma look_law (a : κ → ι) (h : C.PosSemidef) :
    MeasurePreserving (look a) (multivariateGaussian 0 C) (multivariateGaussian 0 (C.submatrix a a)) := by
  refine ⟨(look a).continuous.measurable,?_⟩
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian, map_zero]
    exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun κ ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have hh (i : κ) : (fun u => inner ℝ ((EuclideanSpace.basisFun κ ℝ).toBasis i) u) ∘
        (look a) = fun u => u (a i) := by funext; simp [PiLp.inner_apply]; rfl
    simp_rw [hh, covariance_eval_multivariateGaussian h,
      covarianceBilin_multivariateGaussian (h.submatrix _)]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  exact IsGaussian.memLp_two_id

/-- `e` may even have repetitions in this identity. Positivity & prices
later require charging *distinct* indices with a real inclusion. -/
theorem margin_law (e : κ → ι) (h : C.PosSemidef) : MeasurePreserving (fun v : Vec ι => v ∘ e)
    (cloud C) (cloud (C.submatrix e e)) := by
  let E (φ : Type) [Fintype φ] := MeasurableEquiv.toLp 2 (Vec φ)
  have hg : Measurable (fun v : Vec ι => v ∘ e) := measurable_pi_lambda _ fun i => measurable_pi_apply _
  refine ⟨hg,?_⟩
  unfold cloud; rw [Measure.map_map hg (show Measurable (ofLp : EuclideanSpace ℝ ι → Vec ι) from (E ι).symm.measurable)]
  rw [← (look_law e h).map_eq, Measure.map_map (show Measurable (ofLp : EuclideanSpace ℝ κ → Vec κ) from (E κ).symm.measurable) (look e).continuous.measurable]
  rfl
end volume



section Upper
open FreeResolvent

/-- Counting upper bound constant, no fake change to Euclidean operator norm. -/
def Peak (C : Next.SectorChange.Gaussian.Table ι) (Q : ℝ) := ∀ v : Vec ι, dotProduct v (C *ᵥ v) ≤ Q*dotProduct v v

namespace Peak
variable {A : Next.SectorChange.Gaussian.Table ι} {Q : ℝ}

lemma from_rows {X : Type*} {D : Cost X} {a : ι → X} {σ : ℝ} (h : D.Schur a a σ Q A) (hσ : 0 ≤ σ) : Peak A Q :=
  fun v => le_trans (le_abs_self _) (schur_qf D a (h.mono hσ le_rfl) v)

lemma project (h : Peak A Q) (e : κ ↪ ι) : Peak (A.submatrix e e) Q := by
  classical
  intro v; simpa only [insertion.dot_compress,insertion.dot_insert _ e.injective] using
    h (insertion e *ᵥ v)

lemma compress_gap [DecidableEq ι] (h : Peak A Q) (hA : A.PosDef) (hq : 0 < Q) :
    FreeResolvent.Gap A⁻¹ Q⁻¹ := by
  let R := Q⁻¹
  refine ⟨fun v => ?_⟩
  let w := A⁻¹ *ᵥ v
  let u := R • v
  have hw : A *ᵥ w = v := by unfold w; rw [mulVec_mulVec,mul_nonsing_inv,one_mulVec]; exact (A.isUnit_iff_isUnit_det).mp hA.isUnit
  have hs : A.transpose=A := Matrix.isHermitian_iff_isSymm.mp hA.1
  have ht : dotProduct w (A *ᵥ u) = dotProduct u v := by
    nth_rw 1 [← hs]; rw [dotProduct_transpose_mulVec, hw]
  have hp := hA.posSemidef.dotProduct_mulVec_nonneg (u-w)
  rw [star_trivial,mulVec_sub,hw,sub_dotProduct,dotProduct_sub,dotProduct_sub,ht, dotProduct_comm w v] at hp
  have he : Q*dotProduct u u = R*dotProduct v v := by
    unfold u R; rw [smul_dotProduct,dotProduct_smul]; simp only [smul_eq_mul]; field_simp
  have hh : dotProduct u v = R*dotProduct v v := smul_dotProduct ..
  change R*_ ≤ dotProduct v w
  rw [hh] at hp; linarith only [hp,(h u).trans_eq he]

end Peak
end Upper
end YM.AnalyticBridge.LocalGaussian
