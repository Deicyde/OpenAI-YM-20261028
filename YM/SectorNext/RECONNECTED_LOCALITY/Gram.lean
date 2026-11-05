import YM.SectorNext.RECONNECTED_LOCALITY.Gaussian

set_option warningAsError false

/-!
# Borel parameter pass and normalizations for window law

Parts need the true local marginals and measurability at dummy completions too.
Convenient way to get these is a Gram-root table for *generating a Gaussian*;
keep separate from any affine determinant multiplier or even from the base
Gram. Here the Gram on regular-color coordinates is the **covariance**, including
inactive completion, under ONE law to be used on both sides of the reconnection.
No locality is either used or got on the root itself! No A-estimate either.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
namespace Window

open Function Filter ProbabilityTheory MeasureTheory WithLp
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def source (ι : Type*) [Fintype ι] : Measure (Z ι) := Measure.pi (fun _ : ι => gaussianReal 0 1)

instance : IsProbabilityMeasure (source ι) := by unfold source; infer_instance

open scoped Classical in
def eyes (ι : Type*) : Cov ι := fun i j => if i=j then 1 else 0

lemma source_says (ι : Type*) [Fintype ι] : Says (source ι) (eyes ι) := by
  classical
  refine ⟨inferInstance,fun t => ?_⟩
  unfold source said
  simp_rw [sumPair,osc_sum]
  rw [integral_fintype_prod_eq_prod (f:=fun i x => osc (x*t i))]
  have he i : (∫ x : ℝ,osc (x*t i) ∂gaussianReal 0 1) = bell (t i*t i) := by
    conv_lhs => arg 2; ext; rw [mul_comm]
    simp only [osc, Complex.ofReal_mul,← charFun_apply_real, charFun_gaussianReal]
    unfold bell
    simp [pow_two]
  rw [Finset.prod_congr rfl (fun i _ => he i),← bell_sum]
  simp [act,eyes,mul_ite]

def gram (R : κ → ι → ℝ) : Cov κ := fun i j => ∑ a,R i a*R j a

open Matrix in
lemma gram_pos [DecidableEq κ] (R : κ → ι → ℝ) : Matrix.PosSemidef (show Matrix κ κ ℝ from Window.gram R) := by
  convert! posSemidef_gram ℝ (fun i : κ => (toLp 2 (R i) : EuclideanSpace ℝ ι)) using 1
  unfold Window.gram Matrix.gram
  ext i j
  change ∑ a,R i a*R j a = inner ℝ (toLp 2 (R i) : EuclideanSpace ℝ ι) (toLp 2 (R j))
  simp only [PiLp.inner_apply, Real.inner_apply]

def pour (R : κ → ι → ℝ) : Measure (Z κ) := (source ι).map (run R)
instance (R : κ → ι → ℝ) : IsProbabilityMeasure (pour R) := by
  unfold pour; exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem pour_says (R : κ → ι → ℝ) : Says (pour R) (gram R) := by
  classical
  rw [show gram R=pushed R (eyes ι) by
    funext i j; unfold gram pushed eyes
    simp [mul_ite]]
  exact (source_says ι).image R

omit [Fintype κ] in
lemma parameter_meas {V : Type*} [MeasurableSpace V] {R : V → κ → ι → ℝ} (h : ∀ i j,Measurable fun x => R x i j)
    (f : V → Z κ → ℝ) (hf : Measurable (uncurry f)) : Measurable (fun x => ∫ z,f x z ∂pour (R x)) := by
  let g (p : V × Z ι) := (p.1,run (R p.1) p.2)
  have hg : Measurable g := measurable_fst.prodMk (measurable_pi_lambda _ fun i : κ => by
    change Measurable (fun p : V × Z ι => ∑ j,p.2 j * R p.1 i j)
    exact Finset.measurable_sum _ (fun j _ =>
      ((show Measurable (fun p : Z ι => p j) by fun_prop).comp measurable_snd).mul ((h _ _).comp measurable_fst)))
  have hi (x : V) : (∫ z,f x z ∂pour (R x)) = ∫ z,uncurry f (g (x,z)) ∂source ι := by
    unfold pour; rw [integral_map (by fun_prop) (show AEStronglyMeasurable (f x) _ from
      (hf.comp measurable_prodMk_left).aestronglyMeasurable)]; rfl
  simp_rw [hi]
  exact (hf.comp hg).stronglyMeasurable.integral_prod_right'.measurable

/-- Identification with Mathlib's multivariate law. -/
lemma mathlib_says [DecidableEq κ] {S : Matrix κ κ ℝ} (hs : S.PosSemidef) :
    Says ((multivariateGaussian 0 S).map (MeasurableEquiv.toLp 2 _).symm) (show Cov κ from S) := by
  let p := MeasurableEquiv.toLp 2 (Z κ)
  let M := (multivariateGaussian (0:EuclideanSpace ℝ κ) S).map p.symm
  change Says M _
  refine ⟨Measure.isProbabilityMeasure_map (by fun_prop),fun t => ?_⟩
  rw [← show ofLp (toLp 2 t : EuclideanSpace ℝ κ)=t from ofLp_toLp .., ← fromEuclid, ofLp_toLp]
  rw [show Measure.map (⇑p) M = _ from p.symm.map_symm_map,charFun_multivariateGaussian hs]
  unfold bell act dotProduct Matrix.mulVec
  simp only [inner_zero_right,Complex.ofReal_zero,zero_mul,zero_sub]
  push_cast
  simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  congrm Complex.exp (-(?_ / 2))
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Window
end YM.SectorNext.Reconnect
