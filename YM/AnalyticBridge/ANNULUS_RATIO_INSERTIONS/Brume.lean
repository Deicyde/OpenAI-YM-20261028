import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.CovBound
import YM.Next.FREE_KERNELS.Lifts


/-!
# Marginal law adapter and physical content of 

Includes L1, no dimension loss from positions not enrolled. Accept
coincidences in projection (for the probability identity only; for
Numeric and estimated moments use distinct physical enrollment).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Prism
open Function Filter ProbabilityTheory WithLp MeasureTheory Matrix Precision
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Schur
open scoped Topology RealInnerProductSpace BigOperators Classical MatrixOrder ENNReal

abbrev L2 (ι : Type) := EuclideanSpace ℝ ι
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Same covariance, true marginal. Like mathlib's finite-subset version,
probe the jointly mapped covariance form on basis pairs. No need
for independent coordinates, nor even a gap. -/
def visits (e : I→V) : L2 V →L[ℝ] L2 I :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x=> toLp 2 fun i=> x (e i)
      map_add' := fun _ _=>rfl
      map_smul' := fun _ _=>rfl }

@[simp] lemma visits_apply (e : I → V) (x : L2 V) (i : I) : visits e x i = x (e i) := rfl
-- tours adapts the Gaussian coordinate marginal proof from Mathlib's measurePreserving_restrict₂_multivariateGaussian (Rémy Degenne and Etienne Marion). Copyright (c) 2026 Rémy Degenne. All rights reserved. Apache-2.0. See NOTICE.
lemma tours (e : I → V) (μ : L2 V) (A : Gaussian.Table V) (hA : A.PosSemidef) :
    MeasurePreserving (visits e) (multivariateGaussian μ A)
      (multivariateGaussian (visits e μ) (A.submatrix e e)) where
  measurable := (visits e).continuous.measurable
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun I ℝ).toBasis fun i j ↦ ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map]
    · have (i : I) : (fun u ↦ ⟪(EuclideanSpace.basisFun I ℝ).toBasis i, u⟫) ∘
          visits e = fun u ↦ u (e i) := by ext; simp [PiLp.inner_apply]
      simp_rw [this, covariance_eval_multivariateGaussian hA,
        covarianceBilin_multivariateGaussian (hA.submatrix _)]
      simp
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    exact IsGaussian.memLp_two_id

/-- Counting arrays, with independent projection cost 1. -/
def pocket (e : I→V) (z : Vec V) : Vec I := z ∘ e
@[fun_prop] lemma measurable_pocket (e : I→V) : Measurable (pocket e) := by unfold pocket Function.comp; fun_prop

lemma pocket_eq (e : I→V) {A : Gaussian.Table V} (h : A.PosSemidef) :
    MeasurePreserving (pocket e) (cloud A) (cloud (A.submatrix e e)) := by
  let X := multivariateGaussian 0 A
  have he := (tours e 0 A h).map_eq
  rw [(visits e).map_zero] at he
  refine ⟨measurable_pocket _,?_⟩
  rw [cloud,cloud,← he,Measure.map_map,Measure.map_map]
  · rfl
  all_goals first | exact (visits e).continuous.measurable | exact measurable_pocket _ | exact (MeasurableEquiv.toLp 2 _).symm.measurable

-- don't require the projector to be an embedding to consume
theorem consumes {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α → β} (h : MeasurePreserving f μ ν) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : β → X) (hg : AEStronglyMeasurable g ν) :
    (Integrable (g ∘ f) μ ↔ Integrable g ν) ∧ (∫ x, g (f x) ∂μ) = ∫ x,g x ∂ν := ⟨h.integrable_comp hg,by
      rw [← h.map_eq, integral_map h.measurable.aemeasurable (by rw [h.map_eq]; exact hg)]⟩

section moments
-- A fixed 1D spare factor; use real exponent, includes empty Π.
private def golden (x : ℝ) : ℝ := Real.exp ((1/4:ℝ)*x^2)
private lemma golden_covered :
    Integrable golden (gaussianReal 0 1) ∧ (∫ x,golden x ∂(gaussianReal 0 1)) ≤ 2 := by
  let μ := gaussianReal 0 1
  let L := (Real.sqrt (2 * Real.pi))⁻¹
  let g (x : ℝ) := L*Real.exp (-(1/4:ℝ)*x^2)
  have hμ : μ = volume.withDensity (gaussianPDF 0 1) := gaussianReal_of_var_ne_zero 0 (by simp)
  have ht : ∀ᵐ x ∂volume, gaussianPDF 0 1 x < ⊤ := ae_of_all _ (fun _=>gaussianPDF_lt_top)
  have hf (x : ℝ) : (gaussianPDF 0 1 x).toReal • golden x = g x := by
    rw [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg ..)]; simp only [smul_eq_mul,golden,gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    rw [mul_assoc,← Real.exp_add]; unfold g L; congr 2; ring
  have hi : Integrable g := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/4)).const_mul _
  have he : (∫ x,g x) ≤ 2 := by
    unfold g L
    rw [integral_const_mul,integral_gaussian,inv_mul_eq_div,div_le_iff₀ (by positivity)]
    refine Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt (by positivity)]; have := Real.pi_pos; linarith
  change Integrable golden μ ∧ (∫ x,golden x ∂μ) ≤ 2
  rw [hμ,integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _) ht,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF _ _) ht]
  simp_rw [hf]; exact ⟨hi,he⟩

/-- Gaussian monitor (not operator l₂, no card or color normalization). -/
def gleam (t : ℝ) (x : Vec V) := Real.exp (t*(x ⬝ᵥ x))
@[fun_prop] lemma measurable_gleam (t : ℝ) : Measurable (α:=Vec V) (gleam t) := by unfold gleam dotProduct; fun_prop
lemma gleam_pos (t : ℝ) (x : Vec V) : 0 < gleam t x := Real.exp_pos _

private theorem coin_mgf :
    Integrable (gleam (1/4)) (coins V) ∧
      (∫ x,gleam (1/4) x ∂(coins V)) ≤ (2:ℝ)^Fintype.card V := by
  have hh : (gleam (V:=V) (1/4)) = fun x => ∏ i, golden (x i) := by
    funext x; unfold gleam golden dotProduct
    rw [← Real.exp_sum,Finset.mul_sum]; simp only [sq]
  rw [hh,coins,integral_fintype_prod_eq_pow golden]
  exact ⟨Integrable.fintype_prod (fun i=>golden_covered.1), pow_le_pow_left₀ (integral_nonneg fun _=>(Real.exp_pos _).le) golden_covered.2 _⟩

def leisure (L : ℝ) := (4*L)⁻¹
lemma leisure_pos {L : ℝ} (hL : 0<L) : 0 < leisure L := by unfold leisure; positivity

lemma gaussian_mgf {C : Gaussian.Table V} (hC : C.PosSemidef) {η L t : ℝ} (h : Numeric C η L)
    (hL : 0<L) (ht : 0≤t) (hv : t≤leisure L) :
    Integrable (gleam t) (cloud C) ∧ (∫ x,gleam t x ∂cloud C) ≤ (2:ℝ)^Fintype.card V := by
  let E := CFC.sqrt C; let f := fun x:Vec V=> E*ᵥx
  have hE : E*E=C := CFC.sqrt_mul_sqrt_self _ hC.nonneg
  have hs : E.IsSymm := Matrix.isHermitian_iff_isSymm.mp (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian
  have hF (x : Vec V) : (f x) ⬝ᵥ (f x)= x ⬝ᵥ (C*ᵥ x) := by
    unfold f; have he := Matrix.dotProduct_transpose_mulVec E x (E*ᵥx); rw [hs.eq,mulVec_mulVec,hE] at he; exact he.symm
  have hu : leisure L * L = 1/4 := by unfold leisure; field_simp
  have hl (x : Vec V) : gleam t (f x) ≤ gleam (1/4) x := by
    unfold gleam; rw [hF]; apply Real.exp_le_exp.mpr
    calc
      _ ≤ t*(L*(x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left (h x).2 ht
      _ ≤ leisure L*(L*(x ⬝ᵥ x)) := mul_le_mul_of_nonneg_right hv (mul_nonneg hL.le (dot_nonneg _))
      _ = _ := by rw [← mul_assoc,hu]
  have hf : Measurable f := acts_meas _
  obtain ⟨ha,hb⟩ := consumes (show MeasurePreserving f (coins V) (cloud C) from ⟨hf,paid C⟩)
    (gleam t) (by fun_prop)
  obtain ⟨hm,hh⟩ := coin_mgf (V:=V)
  have he : Integrable ((gleam t) ∘ f) (coins V) := hm.mono' ((measurable_gleam _).comp hf).aestronglyMeasurable
    (ae_of_all _ (fun i=> by rw [Function.comp_apply,Real.norm_of_nonneg (gleam_pos t (f i)).le]; exact hl i))
  rw [← ha, ← hb]; exact ⟨he,(integral_mono he hm hl).trans hh⟩

/-- cost on any finite number of distinct enrolled *keys*
also when still using under Y from actual sector. Drop the untouched keys
before paying for the tilt. -/
theorem pockets {C : Gaussian.Table V} {η L t : ℝ}
    (hL : 0<L) (hC : C.PosSemidef) (hx : Numeric C η L) (hT : 0≤t) (ht : t≤leisure L)
    (e : I → V) (hf : Function.Injective e) : let u := (gleam t) ∘ pocket e
      Integrable u (cloud C) ∧ (∫ z, u z ∂cloud C) ≤ (2:ℝ)^Fintype.card I := by
  intro u
  have he := pocket_eq e hC
  obtain ⟨hh,hl⟩ := consumes he (gleam t) (measurable_gleam _).aestronglyMeasurable
  have ht := gaussian_mgf (hC.submatrix e) (nominated e hf hx) hL hT ht
  exact ⟨hh.mpr ht.1,hl.trans_le ht.2⟩
end moments
end YM.AnalyticBridge.AnnulusRatioInsertions.Prism
