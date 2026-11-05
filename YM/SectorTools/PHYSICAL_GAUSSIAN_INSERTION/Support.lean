import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Completed
import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Moment


/-!
# Local precision-and-source cuts

`Confined`: LOCAL in the Gaussian variable at fixed geometry, body, centers
and other parameters. It is the **difference of quadratic potentials** to
which to apply this support hypothesis, not a covariance window, an
observable read set, or a bare displacement of the mean. Indeed the mean
can move outside the patch. Use `Completed.marginal` to integrate out the
complement, retaining the actual non-product law (the marginal precision is
the inverse of the covariance submatrix, not assumed the precision
submatrix). Prove the likelihood is that of this projected experiment.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SectorTools.PhysicalGaussianInsertion

open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment (Completed.marginal)
open FreeResolvent (insertion)
open scoped Topology BigOperators Classical ENNReal

variable {ι : Type}

def observe (S : Finset ι) (z : Vec ι) : Vec S := fun i => z i

def marginalCov (S : Finset ι) (C : Gaussian.Table ι) := C.submatrix ((↑) : S → ι) ((↑) : S → ι)

lemma observe_sub (S : Finset ι) (x y : Vec ι) : observe S (x-y) = observe S x - observe S y := rfl

variable [Fintype ι] [DecidableEq ι]

/-- Counting-space zero extension. Not embedding a Gaussian with zero
covariance outside `S`. -/
def expandVec (S : Finset ι) (u : Vec S) : Vec ι := insertion ((↑) : S → ι) *ᵥ u

def maskVec (S : Finset ι) (z : Vec ι) : Vec ι := expandVec S (observe S z)

def maskForm (S : Finset ι) (A : Gaussian.Table ι) : Gaussian.Table ι :=
  let I := insertion ((↑) : S → ι)
  I * marginalCov S A * I.transpose

variable {S : Finset ι}

lemma transpose_mul_vec (S : Finset ι) (x : Vec ι) :
    (insertion ((↑) : S → ι)).transpose *ᵥ x = observe S x := by
  ext i
  simp [observe, insertion, mulVec, dotProduct, ite_mul]

omit [Fintype ι] in
lemma continuous_expandVec : Continuous (expandVec S) := by
  unfold expandVec mulVec dotProduct
  fun_prop

lemma observe_expandVec (S : Finset ι) (z : Vec S) : observe S (expandVec S z) = z := by
  rw [← transpose_mul_vec, expandVec, mulVec_mulVec,
    FreeResolvent.insertion.orthogonal _ Subtype.val_injective, one_mulVec]

omit [Fintype ι] in
lemma expandVec_of_not_mem (u : Vec S) (i : ι) (hi : i ∉ S) : expandVec S u i = 0 := by
  have hj (j : S) : (j : ι) ≠ i := fun h => hi (h ▸ j.property)
  unfold expandVec
  simp [mulVec, dotProduct, insertion, hj]

lemma expandVec_quad (S : Finset ι) (A : Gaussian.Table ι) (z : Vec S) :
    quad A (expandVec S z) = quad (marginalCov S A) z :=
  FreeResolvent.insertion.dot_compress _ A z z



lemma maskVec_apply (z : Vec ι) (i : ι) : maskVec S z i = if i ∈ S then z i else 0 := by
  unfold maskVec
  split
  next h => exact congrFun (observe_expandVec S (observe S z)) ⟨i,h⟩
  next h => exact expandVec_of_not_mem _ i h

lemma dot_maskVec (z y : Vec ι) : z ⬝ᵥ maskVec S y = maskVec S z ⬝ᵥ y := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [maskVec_apply y i, maskVec_apply z i]; split <;> simp

omit [Fintype ι] in
lemma maskForm_symm {Q : Gaussian.Table ι} (hQ : Q.IsSymm) : (maskForm S Q).IsSymm := by
  have hh : (marginalCov S Q).IsSymm := hQ.submatrix _
  unfold Matrix.IsSymm maskForm
  dsimp only
  rw [transpose_mul, transpose_mul, hh.eq, transpose_transpose, ← Matrix.mul_assoc]

lemma maskForm_quad (Q : Gaussian.Table ι) (z : Vec ι) :
    quad (maskForm S Q) z = quad Q (maskVec S z) := by
  let I := insertion ((↑) : S → ι)
  rw [maskVec, expandVec_quad]
  change z ⬝ᵥ ((I * marginalCov S Q * I.transpose) *ᵥ z) =
    observe S z ⬝ᵥ _
  rw [← mulVec_mulVec, ← mulVec_mulVec, show I.transpose *ᵥ z = observe S z from
    transpose_mul_vec S z, dotProduct_comm z,
    FreeResolvent.insertion.dot_push, transpose_mul_vec, dotProduct_comm]

omit [Fintype ι] in
lemma maskForm_apply_of_not_mem (Q : Gaussian.Table ι) {i j : ι} (h : i ∉ S ∨ j ∉ S) :
    maskForm S Q i j = 0 := by
  rcases h with h|h
  · have hi (k : S) : (k : ι) ≠ i := fun e => h (e ▸ k.property)
    simp [maskForm, Matrix.mul_apply, insertion, hi]
  have hj (k : S) : (k : ι) ≠ j := fun e => h (e ▸ k.property)
  simp [maskForm, Matrix.mul_apply, insertion, hj]

lemma marginalCov_maskForm (S : Finset ι) (Q : Gaussian.Table ι) :
    marginalCov S (maskForm S Q) = marginalCov S Q := by
  let e : S → ι := (↑)
  let I := insertion e
  let A := marginalCov S Q
  have he : I.transpose * I = 1 := FreeResolvent.insertion.orthogonal e Subtype.val_injective
  calc
    _ = I.transpose * (I*A*I.transpose) * I := (FreeResolvent.insertion.compress e _).symm
    _ = A := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, he, Matrix.one_mul,
      Matrix.mul_assoc, he, Matrix.mul_one]

/-- Difference of PRECISIONS supported in S×S, and relative linear source
supported in S (zero for unchanged centers). `h = d - a`. -/
structure Confined (S : Finset ι) (A D : Gaussian.Table ι) (h : Vec ι) : Prop where
  form_out (i j : ι) : i ∉ S ∨ j ∉ S → (D⁻¹ - A⁻¹) i j = 0
  source_out (i : ι) : i ∉ S → (A⁻¹ *ᵥ h) i = 0

variable {A D : Gaussian.Table ι} {a d h : Vec ι} {p q : ℝ}

lemma Confined.local_variation (hA : A.PosDef) (hl : Confined S A D h) (z : Vec ι) :
    variation A D h z = variation A D h (maskVec S z) := by
  rw [variation_expand hA, variation_expand hA]
  let M := D⁻¹ - A⁻¹
  let b := A⁻¹ *ᵥ h
  have he : maskForm S M = M := by
    ext i j
    by_cases hu : i ∈ S ∧ j ∈ S
    · exact congrFun (congrFun (marginalCov_maskForm S M) ⟨i,hu.1⟩) ⟨j,hu.2⟩
    have hs := not_and_or.mp hu
    rw [maskForm_apply_of_not_mem M hs, show M i j = 0 from hl.form_out _ _ hs]
  have hb : maskVec S b = b := funext fun i => by
    rw [maskVec_apply]; split
    · rfl
    next h => exact (hl.source_out i h).symm
  change quad M _ / _ - z ⬝ᵥ b = _
  rw [show quad M z = _ from he ▸ maskForm_quad M z,
    show z ⬝ᵥ b = _ from hb ▸ dot_maskVec z b]

lemma Confined.local_likelihood (hA : A.PosDef) (hl : Confined S A D (d-a)) (z : Vec ι) :
    likelihood A D a d z = likelihood A D a d (maskVec S z) := by
  rw [likelihood_around z, likelihood_around (maskVec S z), hl.local_variation hA,
    hl.local_variation hA (maskVec S z-d)]
  congr 3
  unfold maskVec
  rw [observe_sub, observe_sub, observe_expandVec]

omit [Fintype ι] [DecidableEq ι] in
lemma marginalCov_pos (S : Finset ι) (hA : A.PosDef) : (marginalCov S A).PosDef :=
  hA.submatrix Subtype.val_injective

/-- Actual correlated Gaussian marginal. -/
lemma preserve_observe (S : Finset ι) (hA : A.PosSemidef) (z : Vec ι) :
    MeasurePreserving (observe S) (law A z) (law (marginalCov S A) (observe S z)) := by
  have hm : Measurable (observe S) := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hf : MeasurePreserving (observe S) (cloud A) (cloud (marginalCov S A)) :=
    Completed.marginal (Embedding.subtype (· ∈ S)) hA
  refine ⟨hm,?_⟩
  rw [law, Measure.map_map hm (law_from_center A z).measurable]
  exact ((law_from_center _ _).comp hf).map_eq

/-- Integrating out the complement identifies the local potential's REAL
likelihood, normalization included. It is the ratio for `marginalCov`, not
that for inverse principal precision blocks. -/
lemma likelihood_local (hA : A.PosDef) (hD : D.PosDef) (hl : Confined S A D (d-a)) (x : Vec ι) :
    likelihood A D a d x = likelihood (marginalCov S A) (marginalCov S D)
      (observe S a) (observe S d) (observe S x) := by
  let H := likelihood A D a d ∘ expandVec S
  have hc : Continuous H := (continuous_likelihood A D a d).comp continuous_expandVec
  let L := likelihood (marginalCov S A) (marginalCov S D) (observe S a) (observe S d)
  have hk : Continuous L := continuous_likelihood ..
  have h x : likelihood A D a d x = H (observe S x) := hl.local_likelihood hA x
  let μ := law (marginalCov S D) (observe S d)
  have hA' := marginalCov_pos S hA
  have hD' := marginalCov_pos S hD
  have hf := preserve_observe S hD.posSemidef d
  have hg := preserve_observe S hA.posSemidef a
  have he : μ.withDensity (fun z => ENNReal.ofReal (H z)) =
      μ.withDensity (fun z => ENNReal.ofReal (L z)) := by
    rw [with_likelihood hA' hD' _ _, ← hg.map_eq, ← with_likelihood hA hD a d]
    ext s hs
    change (law _ _).withDensity _ s = _
    rw [Measure.map_apply hf.measurable hs, withDensity_apply _ hs,
      withDensity_apply _ (hf.measurable hs), ← hf.map_eq,
      setLIntegral_map hs hc.measurable.ennreal_ofReal hf.measurable]
    simp_rw [h]
  have h' := (withDensity_eq_iff_of_sigmaFinite hc.measurable.ennreal_ofReal.aemeasurable
    hk.measurable.ennreal_ofReal.aemeasurable).mp he
  have hv : H =ᵐ[μ] L := by
    filter_upwards [h'] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff
      (likelihood_pos hA hD .. |>.le) (likelihood_pos hA' hD' .. |>.le)).mp hx
  haveI : μ.IsOpenPosMeasure := law_isOpenPosMeasure hD' _
  exact (h x).trans (congrFun (Measure.eq_of_ae_eq hv hc hk) _)

lemma integral_observe (hD : D.PosSemidef) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : Vec S → X} (he : AEStronglyMeasurable F (law (marginalCov S D) (observe S d))) :
    ∫ x, F (observe S x) ∂law D d = ∫ z, F z ∂law (marginalCov S D) (observe S d) := by
  have ht := preserve_observe S hD d
  rw [← ht.map_eq] at he ⊢
  exact (integral_map ht.aemeasurable he).symm

/-- Necessary and sufficient condition from the LOCAL data. Includes the
empty support and exact threshold. -/
lemma power_iff_local (hA : A.PosDef) (hD : D.PosDef) (hl : Confined S A D (d-a)) :
    Integrable (fun x => likelihood A D a d x ^ p) (law D d) ↔
      (mixed (marginalCov S A) (marginalCov S D) p).PosDef := by
  let F (x : Vec S) := likelihood (marginalCov S A) (marginalCov S D) (observe S a)
    (observe S d) x ^ p
  simp_rw [likelihood_local hA hD hl]
  have hm : Measurable F := (continuous_likelihood ..).measurable.pow_const p
  exact ((preserve_observe S hD.posSemidef d).integrable_comp hm.aestronglyMeasurable).trans
    (power_iff (marginalCov_pos S hA) (marginalCov_pos S hD))

lemma mixed_local (hA : A.PosDef) (hD : D.PosDef) (hl : Confined S A D (d-a)) :
    (mixed A D p).PosDef ↔ (mixed (marginalCov S A) (marginalCov S D) p).PosDef :=
  (power_iff hA hD).symm.trans (power_iff_local hA hD hl)

lemma power_integral_local (hA : A.PosDef) (hD : D.PosDef) (hl : Confined S A D (d-a))
    (hm : (mixed (marginalCov S A) (marginalCov S D) p).PosDef) :
    Integrable (fun x => likelihood A D a d x ^ p) (law D d) ∧
      (∫ x, likelihood A D a d x ^ p ∂law D d) =
        moment (marginalCov S A) (marginalCov S D) p (observe S (d-a)) := by
  refine ⟨(power_iff_local hA hD hl).mpr hm,?_⟩
  obtain ⟨hh,he⟩ := power_integral (marginalCov_pos S hA) (marginalCov_pos S hD) hm
    (observe S a) (observe S d)
  simp_rw [likelihood_local hA hD hl]
  exact (integral_observe hD.posSemidef hh.1).trans he

lemma moment_local (hA : A.PosDef) (hD : D.PosDef) (hl : Confined S A D (d-a))
    (hm : (mixed (marginalCov S A) (marginalCov S D) p).PosDef) :
    moment A D p (d-a) = moment (marginalCov S A) (marginalCov S D) p (observe S (d-a)) :=
  (power_integral hA hD ((mixed_local hA hD hl).mpr hm) a d).2.symm.trans
    (power_integral_local hA hD hl hm).2








variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {F : Vec ι → X}





end YM.SectorTools.PhysicalGaussianInsertion
