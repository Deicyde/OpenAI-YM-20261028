import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import YM.MultiNext.VACUUM_STABILITY.Gaussian.Laplace
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian




/-!
# Gaussian calculus on the actual probability space

Use covariance one on the auxiliary/counting coordinates (differentiated
rows in the actual rule below act on its linear images). No nonsingular
precision needed for the tree identity. Tame bounds below are used only to
justify integrability and differentiation, *not* with their constants in
estimates at a variable period.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory ProbabilityTheory Function Filter Finset Set
open YM.Multi.Vacuum.Gauss YM.Next.SectorChange
open scoped Topology BigOperators MatrixOrder ENNReal

variable {I J : Type} [Fintype I] [Fintype J]

/-- Continuous real linear coordinate evaluation. -/
def plane (q : Row J) : Row J →L[ℝ] ℝ := ∑ i, q i • ContinuousLinearMap.proj (R:=ℝ) i

lemma plane_read (q x : Row J) : plane q x=crossed q x := by
  rw [plane, _root_.sum_apply]; rfl

lemma crossed_cont (q : Row J) : Continuous (crossed q) := (funext (plane_read q)) ▸ (plane q).continuous
lemma crossed_deriv (q x : Row J) : HasFDerivAt (crossed q) (plane q) x := by
  rw [← funext (plane_read q)]
  exact ContinuousLinearMap.hasFDerivAt _

lemma csq (x y : Row J) : crossed x y ^ 2 ≤ squares x * squares y := Finset.sum_mul_sq_le_sq_mul_sq ..
lemma squares_nn (x : Row J) : 0 ≤ squares x := sum_nonneg fun _ _ => sq_nonneg _
lemma crossed_self (x : Row J) : crossed x x=squares x := by simp only [crossed,squares,pow_two]
lemma crossed_comm (x y : Row J) : crossed x y=crossed y x := sum_congr rfl fun _ _ => mul_comm ..

lemma squares_deriv (x : Row J) : HasFDerivAt squares ((2:ℝ) • plane x) x := by
  unfold squares plane
  rw [Finset.smul_sum]
  change HasFDerivAt _ (∑ i,(2:ℝ) • x i • ContinuousLinearMap.proj i) x
  convert! HasFDerivAt.sum (u:=univ) (fun i _ => ((hasFDerivAt_apply (𝕜:=ℝ) i x).pow 2)) using 1
  · ext x; simp
  apply sum_congr rfl; intro i _; rw [smul_smul]; simp

variable [DecidableEq J]
-- Adapt the actual measure identity to standard
lemma standard_cloud : standard J = Gaussian.cloud 1 := by
  have he := Gaussian.paid (1 : Gaussian.Table J)
  simp_rw [CFC.sqrt_one,Matrix.one_mulVec] at he
  rwa [Measure.map_id'] at he

def skin (J : Type) [Fintype J] [DecidableEq J] : Row J → ℝ := Gaussian.ratio 1

lemma skin_pos (x : Row J) : 0 < skin J x := Gaussian.ratio_pos Matrix.PosDef.one _
lemma skin_meas : Measurable (skin J) := Gaussian.measurable_ratio _

lemma skin_apply (x : Row J) : skin J x=(Gaussian.coat (1 : Gaussian.Table J))⁻¹ *
    Real.exp ((-(2:ℝ)⁻¹)*squares x) := by
  unfold skin Gaussian.ratio Gaussian.force; rw [inv_one,Matrix.one_mulVec]
  rw [← crossed_self x]; change _ * Real.exp (-crossed x x/2) = _; ring_nf

lemma skin_deriv (x : Row J) : HasFDerivAt (skin J) ((-(skin J x)) • plane x) x := by
  have h1 := (((squares_deriv x).const_mul (-(2:ℝ)⁻¹)).exp.const_mul
      ((Gaussian.coat (1 : Gaussian.Table J))⁻¹))
  simp_rw [skin_apply]
  rw [funext (skin_apply (J:=J))]
  convert! h1 using 1
  ext y; simp
  ring

lemma standard_density : standard J=volume.withDensity (fun x => ENNReal.ofReal (skin J x)) :=
  standard_cloud.trans (Gaussian.cloud_formula Matrix.PosDef.one)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cash (g : Row J → E) :
    (Integrable g (standard J) ↔ Integrable (fun x => skin J x • g x)) ∧
    (∫ x,g x ∂standard J) = ∫ x, skin J x • g x := by
  have hf : Measurable fun x : Row J => ENNReal.ofReal (skin J x) := skin_meas.ennreal_ofReal
  have hb : ∀ᵐ x ∂(volume : Measure (Row J)), ENNReal.ofReal (skin J x) < ⊤ :=
    Filter.Eventually.of_forall fun x => by simp
  rw [standard_density, integrable_withDensity_iff_integrable_smul' hf hb,
      integral_withDensity_eq_integral_toReal_smul hf hb]
  have he x := ENNReal.toReal_ofReal (skin_pos (J:=J) x).le
  simp_rw [he]; simp

omit [DecidableEq J] in
/-- No constant lost to the skin or Banach norm. -/
theorem weighted_stein (w : Row J) (g : Row J → E) (h : Differentiable ℝ g)
    (hg : Integrable g (standard J))
    (hi : Integrable (fun x => crossed w x • g x) (standard J))
    (hd : Integrable (fun x => fderiv ℝ g x w) (standard J)) :
    (∫ x,crossed w x • g x ∂standard J) = ∫ x, fderiv ℝ g x w ∂standard J := by
  classical
  have he (x : Row J) : fderiv ℝ (skin J) x w • g x = - (skin J x • crossed w x • g x) := by
    rw [(skin_deriv x).fderiv, smul_apply, plane_read, crossed_comm x w,
        smul_eq_mul, neg_mul, neg_smul, smul_smul]
  have h₁ : Integrable (fun x => fderiv ℝ (skin J) x w • g x) := by
    simp_rw [he]; exact ((cash _).1.mp hi).neg
  have hk := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h₁ ((cash _).1.mp hd)
    ((cash _).1.mp hg) (fun x _ => (skin_deriv x).differentiableAt) (fun x _ => h x)
  rw [(cash _).2,(cash _).2]
  simp_rw [he,integral_neg,neg_neg] at hk
  exact hk.symm
end YM.Primitives.GCC
