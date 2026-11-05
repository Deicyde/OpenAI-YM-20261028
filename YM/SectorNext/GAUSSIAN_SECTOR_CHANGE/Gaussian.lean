import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Work.F05.PiDensity




set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Normalization in *counting* coordinates

Use only with CompleteSpace codomains.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Gaussian
open Function Filter Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped Topology ENNReal BigOperators MatrixOrder RealInnerProductSpace

abbrev Vec (ι : Type) := ι → ℝ
variable {ι : Type} [Fintype ι] [DecidableEq ι]
abbrev Table (ι : Type) := Matrix ι ι ℝ

/-- Specify by the library's actual probability Gaussian. Transport
from WithLp without changing any coordinate, not a comparison up to
isotropic constants; now volumes use bare product conventions. -/
def cloud (C : Table ι) := (multivariateGaussian 0 C).map (ofLp : EuclideanSpace ℝ ι → Vec ι)

private def naked : EuclideanSpace ℝ ι ≃ᵐ Vec ι := (MeasurableEquiv.toLp 2 (ι → ℝ)).symm
private lemma naked_ap : (naked (ι:=ι) : EuclideanSpace ℝ ι → Vec ι) = ofLp := rfl

lemma preserving_cloud (C : Table ι) : MeasurePreserving naked (multivariateGaussian 0 C) (cloud C) :=
  ⟨naked.measurable,rfl⟩

instance (C : Table ι) : IsProbabilityMeasure (cloud C) :=
  Measure.isProbabilityMeasure_map naked.measurable.aemeasurable

lemma cloud_cov (C : Table ι) (h : C.PosDef) (i j : ι) :
    covariance (fun x : Vec ι => x i) (fun x => x j) (cloud C) = C i j := by
  unfold cloud
  rw [← naked_ap, covariance_map]
  · exact covariance_eval_multivariateGaussian h.posSemidef i j
  · exact (measurable_pi_apply _).aestronglyMeasurable
  · exact (measurable_pi_apply _).aestronglyMeasurable
  exact naked.measurable.aemeasurable

lemma cloud_center (C : Table ι) (i : ι) : (∫ x : Vec ι, x i ∂cloud C)=0 := by
  rw [← (preserving_cloud C).integral_comp' (fun x => x i)]
  change (∫ x, EuclideanSpace.proj i x ∂multivariateGaussian (0 : EuclideanSpace ℝ ι) C)=0
  let L : EuclideanSpace ℝ ι →L[ℝ] ℝ := EuclideanSpace.proj i
  apply (L.integral_comp_id_comm (μ:=multivariateGaussian 0 C) IsGaussian.integrable_id).trans
  rw [integral_id_multivariateGaussian, map_zero]

-- linear algebra of sqrt(C), no norm equivalence constants in det
private lemma root_sq {C : Table ι} (h : C.PosDef) : CFC.sqrt C * CFC.sqrt C = C :=
  CFC.sqrt_mul_sqrt_self C h.posSemidef.nonneg

private lemma root_sym (C : Table ι) : (CFC.sqrt C).IsSymm :=
  Matrix.isHermitian_iff_isSymm.mp (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian

private lemma root_det {C : Table ι} (h : C.PosDef) :
    (CFC.sqrt C).det ^ 2 = C.det := by rw [sq, ← det_mul, root_sq h]

private lemma root_unit {C : Table ι} (h : C.PosDef) : IsUnit (CFC.sqrt C).det := by
  apply IsUnit.mk0 _
  have he := h.det_pos
  have hh := root_det h
  intro hx; simp [hx] at hh; linarith

private lemma root_abs_det {C : Table ι} (h : C.PosDef) :
    |(CFC.sqrt C).det| = Real.sqrt (det C) := by rw [← root_det h, Real.sqrt_sq_eq_abs]

/-- Inverse quadratic form on *vectors*, including momentum-zero if
present there; the cloud has not been conditioned. -/
def force (C : Table ι) (x : Vec ι) : ℝ := x ⬝ᵥ (C⁻¹ *ᵥ x)

private lemma root_back {C : Table ι} (h : C.PosDef) (x : Vec ι) :
    ∑ i, ((CFC.sqrt C)⁻¹ *ᵥ x) i ^ 2 = force C x := by
  let E := CFC.sqrt C
  have he : E * E=C := root_sq h
  have hs : E.transpose=E := root_sym C
  have ht : E⁻¹.transpose=E⁻¹ := by rw [Matrix.transpose_nonsing_inv,hs]
  unfold force
  change ∑ i, (E⁻¹ *ᵥ x) i ^ 2 = _
  rw [← he, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  have hm := Matrix.dotProduct_transpose_mulVec E⁻¹ x (E⁻¹ *ᵥ x)
  rw [ht] at hm
  simpa only [sq,dotProduct] using hm.symm

@[fun_prop] lemma acts_meas (C : Table ι) : Measurable (fun v => C *ᵥ v) := by
  simp_rw [← Matrix.toLin'_apply]; exact (Matrix.toLin' C).continuous_on_pi.measurable

def coins (ι : Type) [Fintype ι] : Measure (Vec ι) := Measure.pi (fun _ => gaussianReal 0 1)

lemma paid (C : Table ι) : (coins ι).map (fun v => CFC.sqrt C *ᵥ v) = cloud C := by
  let L : Vec ι ≃ᵐ EuclideanSpace ℝ ι := naked.symm
  have hL : (coins ι).map L = stdGaussian (EuclideanSpace ℝ ι) := map_pi_eq_stdGaussian
  let E := CFC.sqrt C
  let f := toEuclideanCLM (𝕜 := ℝ) E
  unfold cloud multivariateGaussian
  simp only [zero_add]
  rw [← hL, Measure.map_map, Measure.map_map]
  · rfl 
  all_goals first | exact L.measurable | exact naked.measurable | exact f.continuous.measurable | exact naked.measurable.comp f.continuous.measurable

def dome (ι : Type) [Fintype ι] : ℝ := (Real.sqrt (2 * Real.pi)) ^ Fintype.card ι
lemma dome_pos : 0 < dome ι := by unfold dome; have h := Real.pi_pos; positivity

def coat (C : Table ι) : ℝ := dome ι * Real.sqrt C.det
lemma coat_pos {C : Table ι} (h : C.PosDef) : 0 < coat C := mul_pos dome_pos (Real.sqrt_pos.2 h.det_pos)

def ratio (C : Table ι) (x : Vec ι) := (coat C)⁻¹ * Real.exp (-(force C x) / 2)
lemma ratio_pos {C : Table ι} (h : C.PosDef) (x) : 0 < ratio C x := mul_pos (inv_pos.2 (coat_pos h)) (Real.exp_pos _)

private def roof (x : Vec ι) : ℝ≥0∞ := ENNReal.ofReal ((dome ι)⁻¹ * Real.exp (-(∑ i, (x i)^2) / 2))
private lemma roof_meas : Measurable (roof (ι:=ι)) := by unfold roof; fun_prop
private lemma coins_charge : coins ι = volume.withDensity (roof (ι:=ι)) := by
  have hs : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    rw [← gaussianReal_of_var_ne_zero 0 one_ne_zero]; infer_instance
  unfold coins; simp_rw [gaussianReal_of_var_ne_zero (v:=1) _ one_ne_zero]
  rw [← Work.F05.piDensity _ _ (fun _ => measurable_gaussianPDF 0 1)]
  congr 1
  funext x
  unfold roof gaussianPDF gaussianPDFReal
  rw [← ENNReal.ofReal_prod_of_nonneg (s:=Finset.univ) (fun i _ => ?_)]
  · simp only [NNReal.coe_one,mul_one,sub_zero,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ, ← Real.exp_sum, neg_div, Finset.sum_neg_distrib, ← Finset.sum_div, dome, inv_pow]
  positivity

lemma cloud_formula {C : Table ι} (h : C.PosDef) :
    cloud C = volume.withDensity (fun x => ENNReal.ofReal (ratio C x)) := by
  let E := CFC.sqrt C
  let L := fun v => E *ᵥ v
  have hL : Measurable L := acts_meas E
  have ht : det E ≠ 0 := (root_unit h).ne_zero
  let Q := ENNReal.ofReal |(det E)⁻¹|
  have hh : (volume : Measure (Vec ι)).map L = Q • volume := by
    have hz : L = (Matrix.toLin' E : Vec ι → Vec ι) := funext fun v => (Matrix.toLin'_apply E v).symm
    rw [hz]; exact Real.map_matrix_volume_pi_eq_smul_volume_pi ht
  have he (v : Vec ι) : E⁻¹ *ᵥ (L v)=v := by unfold L; rw [mulVec_mulVec, E.nonsing_inv_mul (root_unit h), one_mulVec]
  ext s hs
  have ha : Measurable fun x : Vec ι => roof (E⁻¹ *ᵥ x) := roof_meas.comp (acts_meas _)
  have hv := setLIntegral_map hs ha hL (μ:=volume)
  simp_rw [he] at hv; rw [hh] at hv
  rw [← paid C, coins_charge, Measure.map_apply hL hs, withDensity_apply _ (hL hs), withDensity_apply _ hs]
  change (∫⁻ v in L ⁻¹' s, roof v) = _
  rw [← hv, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← lintegral_const_mul _ ha]
  have hx (x : Vec ι) : Q * roof (E⁻¹ *ᵥ x) = ENNReal.ofReal (ratio C x) := by
    unfold Q roof ratio coat E
    rw [abs_inv, root_abs_det h, root_back h, ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _)),mul_inv]
    ring_nf
  simp_rw [hx]

@[fun_prop] lemma measurable_ratio (C : Table ι) : Measurable (ratio C) := by
  unfold ratio force
  have h i : Measurable (fun x : Vec ι => (C⁻¹ *ᵥ x) i) := (measurable_pi_apply _).comp (acts_meas _)
  unfold dotProduct; fun_prop (disch := assumption)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Reciprocal density price. No measurability assumption needed: if
using with nontrivial Bochner value will practically want L¹ on one
side (then gets it on the other). -/
lemma under_cloud {C : Table ι} (h : C.PosDef) (f : Vec ι → X) :
    let u := fun x => Real.exp ((force C x)/2) • f x
    (Integrable f ↔ Integrable u (cloud C)) ∧
      (∫ x, f x) = coat C • ∫ x, u x ∂cloud C := by
  intro u
  have hm : Measurable (fun x => ENNReal.ofReal (ratio C x)) := (measurable_ratio _).ennreal_ofReal
  have ht : ∀ᵐ x ∂volume, ENNReal.ofReal (ratio C x) < ⊤ := Filter.Eventually.of_forall fun _ => by simp
  have he (x : Vec ι) : (ENNReal.ofReal (ratio C x)).toReal • u x = (coat C)⁻¹ • f x := by
    unfold u
    rw [smul_smul, ENNReal.toReal_ofReal (ratio_pos h _).le,ratio, mul_assoc,neg_div,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
  rw [cloud_formula h,integrable_withDensity_iff_integrable_smul' hm ht,
    integral_withDensity_eq_integral_toReal_smul hm ht]
  simp_rw [he,integral_smul,smul_smul,mul_inv_cancel₀ (coat_pos h).ne',one_smul,and_true]
  constructor
  · intro h; exact h.smul _
  intro hx
  have hl := hx.smul (coat C)
  change Integrable (coat C • (coat C)⁻¹ • f) volume at hl
  simpa [smul_smul,(coat_pos h).ne'] using hl

lemma paid_scale {g : ℝ} (hg : 0 < g) (f : Vec ι → X) (m : Vec ι) :
    (Integrable f ↔ Integrable (fun x => f (m+g • x))) ∧
      (∫ y, f y) = g ^ Fintype.card ι • ∫ x : Vec ι, f (m+g • x) := by
  let μ : Measure (Vec ι) := volume
  let u := fun x => f (m+x)
  let A : Vec ι ≃ᵐ Vec ι := MeasurableEquiv.addLeft m
  have ha : MeasurePreserving A μ μ := measurePreserving_add_left ..
  change (Integrable f μ ↔ Integrable (fun x => u (g • x)) μ) ∧
    _ = _ • ∫ x, u (g • x) ∂μ
  constructor
  · rw [integrable_comp_smul_iff μ u hg.ne']
    exact (ha.integrable_comp_emb A.measurableEmbedding).symm
  rw [Measure.integral_comp_smul_of_nonneg μ u _ (hR:=hg.le), Module.finrank_pi,
    show (∫ x, u x ∂μ) = ∫ x, f x from ha.integral_comp' f, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hg.ne'), one_smul]

/-- Counts every coordinate (incl zero-dimensional case). -/
theorem gauged {C : Table ι} (h : C.PosDef) {g : ℝ} (hg : 0 < g) (m : Vec ι) (f : Vec ι → X) :
    let u := fun x => Real.exp ((force C x)/2) • f (m+g • x)
    (Integrable f ↔ Integrable u (cloud C)) ∧
    (∫ y, f y) = (g ^ Fintype.card ι * coat C) • ∫ x, u x ∂cloud C := by
  obtain ⟨h1,h2⟩ := paid_scale hg f m
  obtain ⟨h3,h4⟩ := under_cloud h (fun x => f (m+g • x))
  exact ⟨h1.trans h3,h2.trans (by rw [h4,smul_smul])⟩

end YM.Next.SectorChange.Gaussian
