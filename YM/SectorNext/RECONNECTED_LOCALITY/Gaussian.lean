import Mathlib.Probability.Distributions.Gaussian.Multivariate

set_option warningAsError false

/-!
# Conditional window Gaussian marginal service

Here Z is the centered variable *after* the substitution, it is
NOT asserted to be the link law. All the probability statements will be conditioned on
that selection's V, tags and Y. Need a true common covariance including inactive completion. Even though it can depend on the global selection, if on the physical coordinates actually read
in components it has the same entries as at standalone completions, and zero cross entries,
prove the push of this ONE Gaussian by the joint read is the product of the local pushes. There is no assertion about splitting a full Z sample on the whole torus, nor recomputing
C when dropping a default. No estimate of moments here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
namespace Window

open Function Filter ProbabilityTheory MeasureTheory WithLp
open scoped BigOperators RealInnerProductSpace

/-- Use actual Lie colors in orthonormal coordinates; at this level no Euclidean norm on the
array is used. Adapter to Mathlib Euclidean below. -/
abbrev Z (ι : Type*) := ι → ℝ
abbrev Cov (ι : Type*) := ι → ι → ℝ

variable {ι κ δ : Type*} [Fintype ι] [Fintype κ] {μ ν : Measure (Z ι)} {C : Cov ι}

def sumPair (z t : Z ι) := ∑ i,z i*t i

def osc (x : ℝ) := Complex.exp ((x:ℂ)*Complex.I)

def said (μ : Measure (Z ι)) (t : Z ι) := ∫ z, osc (sumPair z t) ∂μ

@[fun_prop] lemma osc_meas : Measurable osc := by unfold osc; fun_prop
@[fun_prop] lemma pair_meas (t : Z ι) : Measurable (fun z => sumPair z t) :=
  by unfold sumPair; fun_prop

@[simp] lemma fromEuclid (μ : Measure (Z ι)) (x : EuclideanSpace ℝ ι) :
    charFun (μ.map (MeasurableEquiv.toLp 2 (Z ι))) x = said μ (ofLp x) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp only [MeasurableEquiv.coe_toLp, PiLp.inner_apply,Real.inner_apply]
  rfl

lemma identify [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : ∀ t,said μ t=said ν t) : μ=ν := by
  apply (MeasurableEquiv.toLp 2 (Z ι)).map_measurableEquiv_injective
  apply Measure.ext_of_charFun (E:=EuclideanSpace ℝ ι)
  funext t; rw [fromEuclid, fromEuclid, h]

/-- Centered real Gaussian law with the supplied covariance. Couple this with a symmetric positive
certificate (otherwise this characteristic function spec only measures the symmetric part of S)
or produce law and C from Gram. TRUE measure identification even when the covariance is singular. -/
def act (C : Cov ι) (x y : Z ι) := ∑ i,∑ j,x i * y j * C i j

def bell (x : ℝ) : ℂ := Complex.exp ((-(x/2) : ℝ) : ℂ)

structure Says (μ : Measure (Z ι)) (C : Cov ι) : Prop where
  normalized : IsProbabilityMeasure μ
  response : ∀ t, said μ t = bell (act C t t)

namespace Says
theorem unique (h : Says μ C) (h' : Says ν C) : μ=ν := by
  have := h.normalized; have := h'.normalized
  exact identify fun _ => (h.response _).trans (h'.response _).symm
end Says

/-- Pull a physical-coordinate law to a list (repeated reads fine, use this actual *joint* law!). -/
def scan (e : κ → ι) (z : Z ι) : Z κ := fun i => z (e i)
omit [Fintype ι] [Fintype κ] in
@[fun_prop] lemma scan_meas (e : κ → ι) : Measurable (scan e) := measurable_pi_lambda _ fun _ => measurable_pi_apply _

def run (R : κ → ι → ℝ) (z : Z ι) : Z κ := fun i => ∑ j,z j*R i j

omit [Fintype κ] in
@[fun_prop] lemma run_meas (R : κ → ι → ℝ) : Measurable (run R) := by
  refine measurable_pi_lambda _ fun i => ?_; change Measurable (fun z : Z ι => ∑ j,z j*R i j)
  fun_prop

def come (R : κ → ι → ℝ) (t : Z κ) : Z ι := fun j => ∑ i,t i*R i j

lemma swap (R : κ → ι → ℝ) (z : Z ι) (t : Z κ) : sumPair (run R z) t = sumPair z (come R t) := by
  unfold sumPair run come; simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_; ring

def pushed (R : κ → ι → ℝ) (C : Cov ι) : Cov κ := fun a b =>
    ∑ i,∑ j,R a i * R b j * C i j

lemma place (R : κ → ι → ℝ) (C : Cov ι) (x y : Z κ) :
    act C (come R x) (come R y) = act (pushed R C) x y := by
  unfold act come pushed; simp only [Finset.sum_mul,Finset.mul_sum]
  -- i j a b -> a b i j
  conv_lhs => arg 2; intro i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  conv_lhs => arg 2; intro i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma said_image (R : κ → ι → ℝ) (μ : Measure (Z ι)) (t : Z κ) :
    said (μ.map (run R)) t = said μ (come R t) := by
  unfold said; rw [integral_map (by fun_prop) (show AEStronglyMeasurable (fun z => osc (sumPair z t)) _ from Measurable.aestronglyMeasurable (osc_meas.comp (pair_meas _)))]; simp_rw [swap R]

lemma Says.image (h : Says μ C) (R : κ → ι → ℝ) : Says (μ.map (run R)) (pushed R C) := by
  have := h.normalized
  exact ⟨Measure.isProbabilityMeasure_map (by fun_prop),fun t => by rw [said_image,h.response,place]⟩

open scoped Classical in
lemma Says.view (h : Says μ C) (e : κ → ι) : Says (μ.map (scan e)) (fun x y => C (e x) (e y)) := by
  let R (x : κ) (i : ι) := if e x=i then (1:ℝ) else 0
  have he : scan e=run R := by funext z x; simp [scan,run,R,Finset.sum_ite_eq]
  have hp : pushed R C = fun x y => C (e x) (e y) := by
    funext x y; unfold pushed R
    simp [ite_mul,mul_ite]
  rw [he,← hp]; exact h.image R

/-- Product across a dependent family of (possibly size zero) coordinate arrays. -/
def ribbon {δ : Type*} (J : δ → Type*) := (MeasurableEquiv.piCurry (fun (d : δ) (_ : J d) => ℝ)).symm

@[simp] lemma ribbon_val {δ : Type*} (J : δ → Type*) (z : (i : δ) → Z (J i)) (x : Sigma J) :
    ribbon J z x = z x.1 x.2 := rfl

variable [Fintype δ] (J : δ → Type*) [∀ d, Fintype (J d)]

lemma osc_sum (x : δ → ℝ) : osc (∑ i,x i) = ∏ i,osc (x i) := by
  unfold osc; rw [Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]

lemma bell_sum (x : δ → ℝ) : bell (∑ i,x i)=∏ i,bell (x i) := by
  unfold bell; rw [Finset.sum_div,← Finset.sum_neg_distrib,Complex.ofReal_sum,Complex.exp_sum]





end Window
end YM.SectorNext.Reconnect
