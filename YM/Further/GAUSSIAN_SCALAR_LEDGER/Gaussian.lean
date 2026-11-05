import Mathlib.Probability.Distributions.Gaussian.Multivariate



set_option warningAsError false

/-!
# Real, finite, normalized Gaussian used in the scalar ledger

`VV i` uses **product Lebesgue** (norm conventions here do not introduce
any counting-volume factors; contrast L²-rescaled fields). Prove exact
density, covariance and Jacobian-with-integrand equations including
integrability. No positive-dimension hypothesis.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function WithLp MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MatrixOrder Topology BigOperators

abbrev VV (ι : Type*) := ι → ℝ
abbrev Wall (ι : Type*) := Matrix ι ι ℝ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fieldLaw (C : Wall ι) : Measure (VV ι) :=
  (multivariateGaussian 0 C).map ((MeasurableEquiv.toLp 2 (VV ι)).symm)

instance (C : Wall ι) : IsProbabilityMeasure (fieldLaw C) := by
  unfold fieldLaw
  apply Measure.isProbabilityMeasure_map
  fun_prop

/-- Normalizing constant in denominator of PDF (sqrt formulation used to
combine with products in the service). -/
def modeCost (C : Wall ι) := Real.sqrt (2 * Real.pi) ^ Fintype.card ι * Real.sqrt C.det

def lawPDF (C : Wall ι) (z : VV ι) := (modeCost C)⁻¹ * Real.exp (-dotProduct z (C⁻¹ *ᵥ z) / 2)

lemma modeCost_pos {C : Wall ι} (h : C.PosDef) : 0 < modeCost C :=
  mul_pos (pow_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)) _)
    (Real.sqrt_pos.mpr h.det_pos)

lemma lawPDF_pos {C : Wall ι} (h : C.PosDef) (z : VV ι) : 0 < lawPDF C z :=
  mul_pos (inv_pos.mpr (modeCost_pos h)) (Real.exp_pos _)

lemma lawPDF_cont (C : Wall ι) : Continuous (lawPDF C) := by
  have he : Continuous (fun v : VV ι => C⁻¹ *ᵥ v) := (toLin' C⁻¹).continuous_of_finiteDimensional
  unfold lawPDF dotProduct
  fun_prop

omit [DecidableEq ι] in
private lemma pi_normal : Measure.pi (fun _ : ι => gaussianReal 0 1) =
    volume.withDensity (fun x : VV ι => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← ofReal_integral_eq_lintegral_ofReal]
  · change ENNReal.ofReal (@integral (VV ι) _ _ _ _ ((Measure.pi (fun _ => volume)).restrict (Set.univ.pi s)) _) = _
    rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
    simp_rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
    apply ENNReal.ofReal_prod_of_nonneg; intro i _
    exact integral_nonneg (gaussianPDFReal_nonneg _ _)
  · exact (Integrable.fintype_prod (f:=fun (_ : ι) => gaussianPDFReal 0 1)
       (μ:=fun _ => volume) (fun _ => integrable_gaussianPDFReal 0 1)).restrict
  filter_upwards with x
  exact Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)

omit [DecidableEq ι] in
private lemma pdf_prod (x : VV ι) :
    (∏ i, gaussianPDFReal 0 1 (x i)) =
      (Real.sqrt (2*Real.pi) ^ Fintype.card ι)⁻¹ * Real.exp (-dotProduct x x / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, inv_pow, ← Real.exp_sum]
  unfold dotProduct
  simp only [pow_two, Finset.sum_neg_distrib, neg_div, ← Finset.sum_div]

/-- Physical determinant appears **once** on all coordinates; show the
Haar consumer uses the actual normalized Gaussian, with full covariance. -/
theorem fieldLaw_density {C : Wall ι} (h : C.PosDef) :
    fieldLaw C = volume.withDensity (fun z => ENNReal.ofReal (lawPDF C z)) := by
  let g := CFC.sqrt C
  have he : g * g = C := CFC.sqrt_mul_sqrt_self _ h.posSemidef.nonneg
  have hl : g.transpose = g := by
    simpa [Matrix.IsHermitian] using (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).1
  have hd : g.det ^ 2 = C.det := by rw [pow_two, ← det_mul, he]
  have hw : g.det ≠ 0 := fun hz => by
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hd
    exact h.det_pos.ne hd
  have hk := mul_nonsing_inv g (isUnit_iff_ne_zero.mpr hw)
  have hM : g.transpose * C⁻¹ * g = 1 := by
    rw [hl]
    have hr := Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr h.det_pos.ne')
    have he' : C⁻¹ * g = g⁻¹ := by
      rw [← mul_one (C⁻¹ * g), ← hk, ← mul_assoc, mul_assoc C⁻¹, he, hr, one_mul]
    rw [mul_assoc, he', hk]
  have hdet : Real.sqrt C.det = |g.det| := by rw [← hd, Real.sqrt_sq_eq_abs]
  let G := toLin' g
  have hg : Measurable (fun x => G x) := G.continuous_of_finiteDimensional.measurable
  have push : fieldLaw C = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map G := by
    unfold fieldLaw multivariateGaussian
    rw [← map_pi_eq_stdGaussian (ι := ι), Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    ext x i
    simp only [Function.comp_apply,zero_add]
    rfl
  let k : VV ι → ℝ := fun x => ∏ i, gaussianPDFReal 0 1 (x i)
  have hline (x : VV ι) : lawPDF C (G x) = |g.det|⁻¹ * k x := by
    have hb : dotProduct (G x) (C⁻¹ *ᵥ (G x)) = dotProduct x x := by
      change dotProduct (g *ᵥ x) _ = _
      have hr : x ⬝ᵥ ((g.transpose * C⁻¹ * g) *ᵥ x) = x ⬝ᵥ x := by rw [hM, one_mulVec]
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at hr
      exact hr
    unfold k lawPDF modeCost
    rw [hb, hdet, pdf_prod, _root_.mul_inv_rev]; ring
  let T : VV ι → ℝ≥0∞ := fun y => ENNReal.ofReal (|g.det| * lawPDF C y)
  have hT : Measurable T := ENNReal.measurable_ofReal.comp (measurable_const.mul (lawPDF_cont C).measurable)
  rw [push, pi_normal]
  ext s hs
  rw [Measure.map_apply hg hs,withDensity_apply _ (hg hs),withDensity_apply _ hs]
  calc
    _ = ∫⁻ x in G ⁻¹' s, T (G x) := by
      apply setLIntegral_congr_fun (hg hs); intro x _
      change ENNReal.ofReal (k x) = ENNReal.ofReal (|det g| * lawPDF C (G x)); rw [hline, mul_inv_cancel_left₀ (abs_pos.mpr hw).ne']
    _ = ∫⁻ y in s, T y ∂Measure.map G volume := (setLIntegral_map hs hT hg).symm
    _ = _ := by
      rw [show Measure.map G volume=ENNReal.ofReal |(det g)⁻¹| • volume from
          Real.map_matrix_volume_pi_eq_smul_volume_pi hw, Measure.restrict_smul, lintegral_smul_measure]
      unfold T
      simp_rw [ENNReal.ofReal_mul (abs_nonneg _)]
      rw [lintegral_const_mul _ ((lawPDF_cont C).measurable.ennreal_ofReal), smul_eq_mul, ← mul_assoc,
        ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, inv_mul_cancel₀ (abs_pos.mpr hw).ne', ENNReal.ofReal_one, one_mul]

lemma integral_law {C : Wall ι} (h : C.PosDef) (g : VV ι → ℝ) :
    (∫ z, g z ∂fieldLaw C) = ∫ z, lawPDF C z * g z := by
  rw [fieldLaw_density h,
      integral_withDensity_eq_integral_toReal_smul ((lawPDF_cont C).measurable.ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (lawPDF_pos h _).le, smul_eq_mul]

lemma integrable_law {C : Wall ι} (h : C.PosDef) (g : VV ι → ℝ) :
    Integrable g (fieldLaw C) ↔ Integrable (fun z => lawPDF C z * g z) := by
  rw [fieldLaw_density h,
      integrable_withDensity_iff_integrable_smul' ((lawPDF_cont C).measurable.ennreal_ofReal) (by simp)]
  simp only [ENNReal.toReal_ofReal (lawPDF_pos h _).le, smul_eq_mul]









omit [DecidableEq ι] in
/-- Scalar version of the affine Lebesgue Jacobian, with integrability.
Charge only *real active coordinates*. -/
theorem moves (g : ℝ) (hg : 0 < g) (μ : VV ι) {f : VV ι → ℝ} (h : Integrable f) :
    Integrable (fun z : VV ι => f (μ + g • z)) ∧
    (∫ a, f a) = g ^ Fintype.card ι * ∫ z : VV ι, f (μ + g • z) := by
  have hi : Integrable (fun z => f (μ + z)) :=
    ((measurePreserving_add_left volume μ).integrable_comp_emb ((Homeomorph.addLeft μ).measurableEmbedding)).mpr h
  have he := Measure.integral_comp_smul_of_nonneg volume (fun z => f (μ + z)) g (hR := hg.le)
  rw [integral_add_left_eq_self,show Module.finrank ℝ (VV ι) = Fintype.card ι from Module.finrank_pi _] at he
  refine ⟨(integrable_comp_smul_iff volume (fun z => f (μ+z)) hg.ne').mpr hi,?_⟩
  rw [he,smul_eq_mul,mul_inv_cancel_left₀ (pow_pos hg _).ne']

/-- Pay both determinant and scale in E real-power convention. -/
lemma modeCost_scale (g : ℝ) (hg : 0 < g) (C : Wall ι) :
    g ^ Fintype.card ι * modeCost C =
      (2 * Real.pi * g^2) ^ ((Fintype.card ι : ℝ) / 2) * Real.sqrt C.det := by
  unfold modeCost
  rw [← mul_assoc, ← mul_pow]
  have he : g * Real.sqrt (2*Real.pi) = (2*Real.pi*g^2) ^ ((1:ℝ)/2) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (x:= 2*Real.pi) (by have := Real.pi_pos; positivity), Real.sqrt_sq hg.le, mul_comm]
  rw [he, ← Real.rpow_natCast, ← Real.rpow_mul (by have := Real.pi_pos; positivity)]
  congr 2; ring

end YM.Further.GaussianScalar
