import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Relative

/-!
# Likelihood of the SectorChange cloud, including the center

On any finite physical counting space, no dimension/occupancy restriction.
Uses `Relative.change`; keeps the direction of the change (in particular the
sign of the displacement), the Lebesgue determinant and quadratic costs, in
an ordinary integral AND measure form. All on normalized laws. Centers given
in the *same units* as the Gaussian variables.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SectorTools.PhysicalGaussianInsertion

open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian (Vec force cloud)
open AnalyticBridge.GaussianFieldAlignment.Relative (trade)
open scoped Topology BigOperators Classical ENNReal

variable {ι : Type} [Fintype ι]

/-- Counting quadratic form (of `Q` itself, not its inverse). -/
def quad (Q : Gaussian.Table ι) (z : Vec ι) : ℝ := z ⬝ᵥ (Q *ᵥ z)

lemma continuous_quad (Q : Gaussian.Table ι) : Continuous (quad Q) := by
  unfold quad mulVec dotProduct
  fun_prop

lemma cross_eq_of_isSymm {Q : Gaussian.Table ι} (h : Q.IsSymm) (x y : Vec ι) :
    x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
  simpa only [h.eq] using dotProduct_transpose_mulVec Q x y

lemma quad_add {Q : Gaussian.Table ι} (h : Q.IsSymm) (x y : Vec ι) :
    quad Q (x + y) = quad Q x + 2 * (x ⬝ᵥ (Q *ᵥ y)) + quad Q y := by
  unfold quad
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    cross_eq_of_isSymm h y x]
  ring

lemma quad_smul (Q : Gaussian.Table ι) (x : Vec ι) (r : ℝ) :
    quad Q (r • x) = r^2 * quad Q x := by
  unfold quad
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

lemma quad_zero (Q : Gaussian.Table ι) : quad Q 0 = 0 := zero_dotProduct _

lemma quad_pos {Q : Gaussian.Table ι} (h : Q.PosDef) {x : Vec ι} (hx : x ≠ 0) : 0 < quad Q x := by
  simpa only [star_trivial, quad] using h.dotProduct_mulVec_pos hx

lemma quad_nonneg {Q : Gaussian.Table ι} (h : Q.PosDef) (x : Vec ι) : 0 ≤ quad Q x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [quad_zero]
  exact (quad_pos h hx).le

lemma posDef_of_quad_pos {Q : Gaussian.Table ι} (h : Q.IsSymm) (hh : ∀ x ≠ 0, 0 < quad Q x) :
    Q.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_iff_isSymm.mpr h) fun x hx => ?_
  rw [star_trivial]
  exact hh x hx

variable [DecidableEq ι] {A C D : Gaussian.Table ι} {a c d : Vec ι}

/-- Actual probability Gaussian, with an explicit affine mean shift `m` in
these same coordinates. We only compare for positive definite covariances. -/
def law (C : Gaussian.Table ι) (m : Vec ι) : Measure (Vec ι) :=
  (cloud C).map (MeasurableEquiv.addLeft m)

lemma law_from_center (C : Gaussian.Table ι) (m : Vec ι) :
    MeasurePreserving (MeasurableEquiv.addLeft m) (cloud C) (law C m) :=
  ⟨(MeasurableEquiv.addLeft m).measurable, rfl⟩



scoped instance (C : Gaussian.Table ι) (m : Vec ι) : IsProbabilityMeasure (law C m) :=
  Measure.isProbabilityMeasure_map (law_from_center C m).measurable.aemeasurable

lemma law_isOpenPosMeasure (hC : C.PosDef) (m : Vec ι) : Measure.IsOpenPosMeasure (law C m) := by
  have hh : (volume : Measure (Vec ι)) ≪ cloud C := by
    rw [Next.SectorChange.Gaussian.cloud_formula hC]
    exact withDensity_absolutelyContinuous'
      (Next.SectorChange.Gaussian.measurable_ratio C |>.ennreal_ofReal.aemeasurable)
      (Eventually.of_forall fun x =>
        (ENNReal.ofReal_pos.mpr (Next.SectorChange.Gaussian.ratio_pos hC x)).ne')
  haveI := hh.isOpenPosMeasure
  exact (show Continuous (fun z : Vec ι => m + z) by fun_prop).isOpenPosMeasure_map
    (MeasurableEquiv.addLeft m).surjective

/-- Likelihood of `(A,a)` relative to `(D,d)`, using `Relative.trade` on
the **reference-centered argument**. Thus the shift in trade is `d - a`,
NOT `a - d`. -/
def likelihood (A D : Gaussian.Table ι) (a d : Vec ι) (x : Vec ι) : ℝ := trade A D (d - a) (x - d)

/-- Centered on the reference. The exact quadratic/affine field in the log
likelihood, with its *constant* part subtracted. -/
def variation (A D : Gaussian.Table ι) (h z : Vec ι) : ℝ :=
  (force D z - force A (h + z) + force A h) / 2



lemma variation_expand (hA : A.PosDef) (z : Vec ι) :
    variation A D a z = quad (D⁻¹ - A⁻¹) z / 2 - z ⬝ᵥ (A⁻¹ *ᵥ a) := by
  have hh := quad_add (isHermitian_iff_isSymm.mp hA.inv.isHermitian) z a
  change (quad _ _ - quad _ _ + quad _ _) / _ = _
  rw [add_comm a z, hh]
  unfold quad
  rw [sub_mulVec, dotProduct_sub]
  ring

lemma continuous_variation (A D : Gaussian.Table ι) (h : Vec ι) : Continuous (variation A D h) := by
  change Continuous (fun z : Vec ι => (quad D⁻¹ z - quad A⁻¹ (h + z) + _) / _)
  exact (((continuous_quad _).sub
    ((continuous_quad _).comp (continuous_const.add continuous_id))).add continuous_const).div_const _

lemma continuous_likelihood (A D : Gaussian.Table ι) (a d : Vec ι) : Continuous (likelihood A D a d) := by
  change Continuous (fun x : Vec ι => _ * Real.exp
    ((quad D⁻¹ (x-d) - quad A⁻¹ ((d-a)+(x-d))) / 2))
  refine continuous_const.mul (Real.continuous_exp.comp ((Continuous.sub ?_ ?_).div_const 2))
  · exact (continuous_quad _).comp (continuous_id.sub continuous_const)
  exact (continuous_quad _).comp (continuous_const.add (continuous_id.sub continuous_const))

lemma likelihood_pos (hA : A.PosDef) (hD : D.PosDef) (a d x : Vec ι) :
    0 < likelihood A D a d x :=
  mul_pos (div_pos (Real.sqrt_pos.mpr hD.det_pos) (Real.sqrt_pos.mpr hA.det_pos))
    (Real.exp_pos _)



lemma likelihood_around (x : Vec ι) :
    likelihood A D a d x = likelihood A D a d d * Real.exp (variation A D (d-a) (x-d)) := by
  unfold likelihood AnalyticBridge.GaussianFieldAlignment.Relative.trade variation
  rw [sub_self, add_zero, show force D (0 : Vec ι) = 0 from quad_zero _]
  rw [mul_assoc, ← Real.exp_add]
  ring_nf



variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
lemma integrable_law (C : Gaussian.Table ι) (a : Vec ι) (f : Vec ι → X) :
    Integrable f (law C a) ↔ Integrable (fun z => f (a + z)) (cloud C) :=
  ((law_from_center C a).integrable_comp_emb (MeasurableEquiv.addLeft a).measurableEmbedding).symm

lemma integral_law (C : Gaussian.Table ι) (a : Vec ι) (f : Vec ι → X) :
    ∫ x, f x ∂law C a = ∫ z, f (a + z) ∂cloud C :=
  ((law_from_center C a).integral_comp' f).symm

/-- Transport `Relative.change`, both integrability and expectation (use with CompleteSpace). -/
lemma affine_change (hA : A.PosDef) (hD : D.PosDef) (a d : Vec ι) (f : Vec ι → X) :
    (Integrable f (law A a) ↔ Integrable (fun x => likelihood A D a d x • f x) (law D d)) ∧
      (∫ x, f x ∂law A a) = ∫ x, likelihood A D a d x • f x ∂law D d := by
  have ht := AnalyticBridge.GaussianFieldAlignment.Relative.change hA hD (d-a)
    (fun z => f (a + z))
  have he z : a + ((d-a)+z) = d+z := by abel
  simp_rw [he] at ht
  rw [integrable_law, integrable_law D, integral_law A a f,
    integral_law D d (fun x => likelihood A D a d x • f x)]
  simpa only [likelihood, add_sub_cancel_left] using ht

lemma likelihood_integral (hA : A.PosDef) (hD : D.PosDef) :
    Integrable (likelihood A D a d) (law D d) ∧ (∫ x, likelihood A D a d x ∂law D d) = 1 := by
  obtain ⟨hh, he⟩ := affine_change hA hD a d (fun _ => (1 : ℝ))
  constructor
  · simpa using hh.mp (integrable_const _)
  simpa using he.symm

/-- RN identity as measures, not assuming equivalence of tag/flag/profile
factors. -/
lemma with_likelihood (hA : A.PosDef) (hD : D.PosDef) (a d : Vec ι) :
    (law D d).withDensity (fun x => ENNReal.ofReal (likelihood A D a d x)) = law A a := by
  classical
  ext s hs
  let f := s.indicator fun _ : Vec ι => (1 : ℝ)
  have he (x : Vec ι) : likelihood A D a d x • f x = s.indicator (likelihood A D a d) x := by
    by_cases h : x ∈ s <;> simp [h, f]
  have hh := (affine_change hA hD a d f).2
  simp_rw [he, integral_indicator hs] at hh
  change (∫ x, s.indicator 1 x ∂law A a) = _ at hh
  rw [integral_indicator_one hs] at hh
  rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal
    (likelihood_integral hA hD).1.integrableOn
    (Eventually.of_forall fun x => (likelihood_pos hA hD a d x).le), ← hh]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)



end YM.SectorTools.PhysicalGaussianInsertion
