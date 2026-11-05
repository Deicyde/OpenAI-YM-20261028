import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian


/-!
# Keeping the actual marginals

Zero *cross* covariance only; no independence hypothesis among the links
read inside one species. Different reads may use different within-A matrices
if one rebooks the sector; that is **not** licensed here.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Projection
open Set Function Filter MeasureTheory ProbabilityTheory Matrix WithLp
open Next.SectorChange.Gaussian (Table Vec cloud)
open scoped Topology BigOperators MatrixOrder RealInnerProductSpace ENNReal Classical

section gaussian
variable {I J K : Type} [Fintype I] [Fintype J] [DecidableEq J] {C : Table J}
  [Fintype K] [DecidableEq K]

private def wideMap (e : K → J) : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ K :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : K => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : K => EuclideanSpace.proj (𝕜:=ℝ) (e i)))

private lemma wide_apply (e : K → J) (x : EuclideanSpace ℝ J) (i : K) :
    wideMap e x i = x (e i) := rfl
-- wide_projection adapts the Gaussian coordinate marginal proof from Mathlib's measurePreserving_restrict₂_multivariateGaussian (Rémy Degenne and Etienne Marion). Copyright (c) 2026 Rémy Degenne. All rights reserved. Apache-2.0. See NOTICE.
private lemma wide_projection (e : K → J) (H : C.PosSemidef) :
    MeasurePreserving (wideMap e) (multivariateGaussian 0 C) (multivariateGaussian 0 (C.submatrix e e)) := by
  refine ⟨Continuous.measurable (wideMap e).continuous,?_⟩
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian, map_zero]
    exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]; refine LinearMap.BilinForm.ext_basis
    (EuclideanSpace.basisFun K ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have h (i : K) : (fun u => ⟪(EuclideanSpace.basisFun K ℝ).toBasis i,u⟫) ∘ wideMap e =
        fun u : EuclideanSpace ℝ J => u (e i) := by
      funext x; rw [Function.comp_apply]; simp [PiLp.inner_apply,wide_apply]
    simp_rw [h, covariance_eval_multivariateGaussian H, covarianceBilin_multivariateGaussian (H.submatrix e)]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

lemma cloud_projection (hC : C.PosDef) (e : K → J) :
    MeasurePreserving (fun y : Vec J => fun i => y (e i)) (cloud C) (cloud (C.submatrix e e)) := by
  let f := fun y : Vec J => fun i : K => y (e i)
  have hf : Measurable f := measurable_pi_lambda _ fun i => measurable_pi_apply _
  refine ⟨hf,?_⟩
  let u := (MeasurableEquiv.toLp 2 (Vec J)).symm
  let v := (MeasurableEquiv.toLp 2 (Vec K)).symm
  change ((multivariateGaussian 0 C).map u).map f = (multivariateGaussian 0 (C.submatrix e e)).map v
  rw [Measure.map_map hf u.measurable,← (wide_projection e hC.posSemidef).map_eq,
    Measure.map_map v.measurable (wideMap e).continuous.measurable]; rfl

/-- Projection on several groups of coordinates, the *only* independence
used for component locality under the normalized Gaussian. -/
lemma independent (hC : C.PosDef) {P : I → Type} [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (e : ∀ i, P i → J) (h : ∀ i j, i ≠ j → ∀ a b, C (e i a) (e j b) = 0) :
    MeasurePreserving (fun y : Vec J => fun i a => y (e i a)) (cloud C)
      (Measure.pi fun i => cloud (C.submatrix (e i) (e i))) := by
  let X (i : I) (y : Vec J) : Vec (P i) := fun a => y (e i a)
  let Z : Measure (Vec J) := cloud C
  have hm (i) : Measurable (X i) := (cloud_projection hC (e i)).measurable
  have hf : HasGaussianLaw (id (α:=Vec J)) Z := by
    have hz : IsGaussian (cloud C) := by
      let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : J => ℝ)
      change IsGaussian ((multivariateGaussian 0 C).map (L : EuclideanSpace ℝ J → Vec J))
      infer_instance
    exact IsGaussian.hasGaussianLaw_id
  let L : Vec J →L[ℝ] (∀ i, Vec (P i)) := ContinuousLinearMap.pi (fun i =>
    ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (R:=ℝ) (e i j)))
  have H : HasGaussianLaw (fun y i => X i y) Z := hf.map L
  have he : iIndepFun X Z := H.iIndepFun_of_covariance_eval (fun i j hij a b =>
    (Next.SectorChange.Gaussian.cloud_cov C hC (e i a) (e j b)).trans (h i j hij a b))
  refine ⟨measurable_pi_lambda _ hm,?_⟩
  change Z.map (fun y i => X i y) = Measure.pi _
  rw [he.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
  exact congr_arg Measure.pi (funext fun i => (cloud_projection hC (e i)).map_eq)
end gaussian

section other
open MeasurableSpace

variable {J I K : Type} [Fintype J] [Fintype I] [Fintype K]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

lemma pi_projection (e : I ↪ J) :
    MeasurePreserving (fun y : J → X => fun i => y (e i))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  let v := Measure.pi fun _ : J => μ
  let H (j : J) (x : J → X) := x j
  have h (i) : MeasurePreserving (H i) v μ := measurePreserving_eval _ _
  have hf : iIndepFun H v := iIndepFun_pi (μ:=fun _ => μ) (X:=fun _ => id) (fun _ => aemeasurable_id)
  let Y (i : I) := H (e i)
  have he : iIndepFun Y v := hf.precomp e.injective
  refine ⟨measurable_pi_lambda _ (fun i => (h (e i)).measurable),?_⟩
  change v.map (fun x i => Y i x) = Measure.pi _
  rw [he.map_fun_eq_pi_map (fun i => (h (e i)).measurable.aemeasurable)]
  exact congr_arg Measure.pi (funext fun i => (h (e i)).map_eq)

lemma arrays {R : I → Type} [∀ i, Fintype (R i)] (e : (i : I) → R i ↪ J)
    (h : ∀ i j, i≠j → ∀ a b,e i a ≠ e j b) :
    MeasurePreserving (fun y : J → X => fun i a => y (e i a))
      (Measure.pi fun _ => μ) (Measure.pi fun i => (Measure.pi fun _ : R i => μ)) := by
  let E : Sigma R ↪ J := ⟨fun u => e u.1 u.2, by
    rintro ⟨i,a⟩ ⟨j,b⟩ hab
    have ht : i=j := Classical.not_not.mp fun hn => h i j hn a b hab
    subst j
    exact congr_arg (Sigma.mk i) ((e i).injective hab)⟩
  let m (x : I) := Measure.pi fun _ : R x => μ
  let S : Measure (Sigma R → X) := Measure.pi fun _ => μ
  let L : (∀ i, R i → X) ≃ᵐ (Sigma R → X) := {
    toFun y a := y a.1 a.2
    invFun y i a := y ⟨i,a⟩
    left_inv _ := rfl
    right_inv _ := rfl
    measurable_toFun := by
      change Measurable (fun (y : (i : I) → R i → X) a => y (Sigma.fst a) (Sigma.snd a))
      exact measurable_pi_lambda _ fun a => (measurable_pi_apply a.2).comp (measurable_pi_apply a.1)
    measurable_invFun := by
      change Measurable (fun (y : Sigma R → X) (i : I) (a : R i) => y ⟨i,a⟩)
      exact measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun i => measurable_pi_apply _ }
  have ht : MeasurePreserving L (Measure.pi m) S := by
    refine ⟨L.measurable,(Measure.pi_eq (μ:=fun _ : Sigma R => μ) fun t ht => ?_).symm⟩
    have hp : L ⁻¹' univ.pi t = univ.pi (fun i : I => univ.pi (fun a : R i => t ⟨i,a⟩)) := by
      ext y
      simp [Set.mem_pi,L,Sigma.forall]
    simp_rw [MeasurableEquiv.map_apply,hp,m,Measure.pi_pi,Fintype.prod_sigma]
  exact ht.symm.comp (pi_projection μ E)
end other

section join
variable {I : Type} [Fintype I] {X Y : I → Type*} [∀ i,MeasurableSpace (X i)]
  [∀ i,MeasurableSpace (Y i)] (μ : ∀ i,Measure (X i)) (ν : ∀ i,Measure (Y i))
  [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]

lemma join :
    MeasurePreserving (fun a : (∀ i,X i) × (∀ i,Y i) => fun i => (a.1 i,a.2 i))
      ((Measure.pi μ).prod (Measure.pi ν)) (Measure.pi (fun i => (μ i).prod (ν i))) := by
  let F := fun a : (∀ i,X i) × (∀ i,Y i) => fun i => (a.1 i,a.2 i)
  have he : Measurable F := measurable_pi_lambda _ fun i => ((measurable_pi_apply _).comp measurable_fst).prodMk
    ((measurable_pi_apply _).comp measurable_snd)
  refine ⟨he, (Measure.pi_eq_generateFrom (μ:=fun i => (μ i).prod (ν i))
    (fun i => generateFrom_prod) (fun i => isPiSystem_prod)
    (fun i => (μ i).toFiniteSpanningSetsIn.prod (ν i).toFiniteSpanningSetsIn) (μν:=(((Measure.pi μ).prod (Measure.pi ν)).map F))
    (fun s hs => ?_)).symm⟩
  choose A hA B hB hb using hs
  have hm i : MeasurableSet (s i) := hb i ▸ MeasurableSet.prod (s:=A i) (t:=B i) (hA i) (hB i)
  rw [Measure.map_apply he (MeasurableSet.univ_pi hm)]
  have hp : F ⁻¹' univ.pi s = univ.pi A ×ˢ univ.pi B := by
    ext y; simp [Set.mem_pi,F,← hb,forall_and]
  rw [hp,Measure.prod_prod]; simp_rw [Measure.pi_pi,← hb, Measure.prod_prod]; rw [Finset.prod_mul_distrib]
end join

section locality

variable {J K I : Type} [Fintype J] [Fintype I] [Fintype K] [DecidableEq K]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {C : Table K}
  {R P : I → Type} [∀ i, Fintype (R i)] [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

variable (hC : C.PosDef) (e : ∀ i, R i ↪ J) (h : ∀ i j, i≠j → ∀ a b,e i a ≠ e j b)
    (p : ∀ i, P i → K) (hc : ∀ i j, i≠j → ∀ a b,C (p i a) (p j b)=0)
    (M : ∀ i, Table (P i)) (hm : ∀ i,C.submatrix (p i) (p i)=M i)
include h hm hc hC

lemma localizes :
    MeasurePreserving (fun y : (J → X) × Vec K => fun i => (fun a => y.1 (e i a),fun b => y.2 (p i b)))
      ((Measure.pi fun _ => μ).prod (cloud C)) (Measure.pi fun i => (Measure.pi fun _ : R i => μ).prod (cloud (M i))) := by
  have hz := independent hC p hc; simp_rw [hm] at hz
  exact (join (fun i => (Measure.pi fun _ : R i => μ)) _).comp ((arrays μ e h).prod hz)

/-- Actual L¹ and literal extraction under the localized reads of the marginal.
Includes empty index types. Even if Y sections are not registered on every dust
fiber. -/
theorem integrals (f : (i : I) → (R i → X) × Vec (P i) → ℝ)
    (hf : ∀ i, Integrable (f i) ((Measure.pi fun _ => μ).prod (cloud (M i)))) :
    let V := (Measure.pi fun _ : J => μ).prod (cloud C)
    let w := fun y : (J → X) × Vec K => ∏ i, f i ((fun a => y.1 (e i a)),fun b => y.2 (p i b))
    Integrable w V ∧ (∫ y,w y ∂V) = ∏ i,∫ y,f i y ∂((Measure.pi fun _ => μ).prod (cloud (M i))) := by
  intro V w
  let F := fun y : (J→X) × Vec K => fun i => ((fun a : R i => y.1 (e i a)),fun b => y.2 (p i b))
  let L := Measure.pi fun i => (Measure.pi fun _ : R i => μ).prod (cloud (M i))
  let G := fun y : (∀ i,(R i→X) × Vec (P i)) => ∏ i, f i (y i)
  have hi := Integrable.fintype_prod_dep hf
  have hh : MeasurePreserving F V L := localizes μ hC e h p hc M hm
  refine ⟨(hh.integrable_comp hi.1).mpr hi,?_⟩
  have hp := integral_fintype_prod_eq_prod f (μ:=fun i => (Measure.pi fun _ => μ).prod (cloud (M i)))
  change (∫ y,G y ∂L)=_ at hp
  rw [← hp,← hh.map_eq,integral_map hh.measurable.aemeasurable]
  exact hh.map_eq.symm ▸ hi.1

end locality
end YM.AnalyticBridge.Sharp.Projection
