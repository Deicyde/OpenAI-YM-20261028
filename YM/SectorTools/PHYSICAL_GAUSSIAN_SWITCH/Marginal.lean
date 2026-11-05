import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Completed
import YM.Next.SCHEDULE.GridCost
import YM.Push.FREE_RESOLVENT.Vertical
import YM.SectorNext.RECONNECTED_LOCALITY.Gram
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.Shift



/-!
# Pay only on a sufficient Gaussian marginal

Measurable statistic on which the likelihood lives, law under target and
reference both known. Two cases below in Local and Schur: raw projection
(producing the actual Gaussian marginal when potential is confined), and a
different, residual projection (for a covariance-confined perturbation).
There is also the different hypothesis of a cylindrical observable: one
needs no confinement of the interaction displacement to compare just those
expectations (nor does that comparison give a price for nonlocal functions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment.Completed (marginal)
open scoped Topology BigOperators ENNReal
local notation "Covar" => Next.SectorChange.Gaussian.Table

attribute [local instance] shift_probability
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

section matrix
/-- Real linear view in counting coordinates; allows exact Schur residual
comparisons without requiring the statistic to pick out literal entries.
The cloud lemma even works if this marginal is singular, though density
ratios below will not be used in that regime. -/
def view (R : Matrix J I ℝ) : Vec I → Vec J := fun x => R *ᵥ x

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma view_cont (R : Matrix J I ℝ) : Continuous (view R) := by unfold view Matrix.mulVec dotProduct; fun_prop

def covView (R : Matrix J I ℝ) (M : Covar I) : Covar J := R * M * R.transpose

omit [DecidableEq I] [DecidableEq J] in
lemma covView_posSemi (R : Matrix J I ℝ) {M : Covar I} (h : M.PosSemidef) : (covView R M).PosSemidef := by
  have he : R.conjTranspose=R.transpose := by ext; simp
  unfold covView; rw [← he]; exact h.mul_mul_conjTranspose_same _

open SectorNext.Reconnect.Window (mathlib_says run pushed)
lemma view_cloud {A : Covar I} (hA : A.PosSemidef) (R : Matrix J I ℝ) :
    MeasurePreserving (view R) (cloud A) (cloud (covView R A)) := by
  refine ⟨(view_cont _).measurable,?_⟩
  have hh := (mathlib_says hA).image R
  have he : view R = run R := by
    ext; unfold run view Matrix.mulVec dotProduct; simp [mul_comm]
  have hy (p q : J) : pushed R (show SectorNext.Reconnect.Window.Cov I from A) p q = covView R A p q := by
    unfold pushed covView; simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [he]
  apply hh.unique
  rw [show pushed R A = _ from funext (fun i => funext fun j => hy i j)]
  exact mathlib_says (covView_posSemi R hA)

private lemma shift_over {R : Vec I → Vec J} {A : Covar I} {T : Covar J} (m : Vec I)
    (h : MeasurePreserving R (cloud A) (cloud T)) (ha : ∀ x, R (m+x)=R m+R x) :
    MeasurePreserving R (shift A m) (shift T (R m)) := by
  refine ⟨h.measurable,?_⟩
  rw [shift,shift,Measure.map_map h.measurable (by fun_prop),← h.map_eq,Measure.map_map (by fun_prop) h.measurable]
  simp only [comp_def,ha]

lemma view_shift {A : Covar I} (hA : A.PosSemidef) (R : Matrix J I ℝ) (m : Vec I) :
    MeasurePreserving (view R) (shift A m) (shift (covView R A) (view R m)) :=
  shift_over m (view_cloud hA R) (fun _ => Matrix.mulVec_add ..)



end matrix

section pull
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {R : X → Y} {ν : Measure Y}

lemma density_pull (hf : MeasurePreserving R μ ν) (f : Y → ℝ≥0∞) (h : Measurable f) :
    Measure.map R (μ.withDensity (fun x => f (R x)))=ν.withDensity f := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hf.measurable hs,withDensity_apply _ (hf.measurable hs),withDensity_apply _ hs,← hf.map_eq,
    setLIntegral_map hs h hf.measurable]

lemma pay_pull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hr : MeasurePreserving R μ ν)
    (f : Y → E) (hf : AEStronglyMeasurable f ν) :
    (Integrable (fun x => f (R x)) μ ↔ Integrable f ν) ∧ (∫ x,f (R x) ∂μ)=∫ y,f y ∂ν := by
  refine ⟨hr.integrable_comp hf,?_⟩
  rw [← hr.map_eq] at hf ⊢; rw [integral_map hr.measurable.aemeasurable hf]
end pull

section reduction
variable (R : Vec I → Vec J) (A : Covar I) (a : Vec I) (D : Covar I) (d : Vec I)
  (S T : Covar J)

/-- Enough to integrate all likelihood powers on a lower dimensional
law; the consumer is license to use those prices with arbitrary other
functions under the *original full normalized laws*. -/
structure Sufficient : Prop where
  a_pos : A.PosDef
  d_pos : D.PosDef
  target : S.PosDef
  reference : T.PosDef
  source : MeasurePreserving R (shift A a) (shift S (R a))
  dest : MeasurePreserving R (shift D d) (shift T (R d))
  depends : ∃ f : Vec J → ℝ, Measurable f ∧ (∀ y, 0 ≤ f y) ∧ likelihood A a D d = f ∘ R

variable {R A a D d S T}
namespace Sufficient
variable (h : Sufficient R A a D d S T)
include h

theorem read :
    likelihood A a D d =ᵐ[shift D d] (fun x => likelihood S (R a) T (R d) (R x)) := by
  obtain ⟨f,hf,hg,he⟩:=h.depends
  let μ:=shift D d; let ν:=shift T (R d)
  have hh : ν.withDensity (fun y => ENNReal.ofReal (f y))=shift S (R a) := by
    rw [← density_pull h.dest _ hf.ennreal_ofReal,← h.source.map_eq]
    simp_rw [show ∀ x, f (R x)=likelihood A a D d x from fun x => (congrFun he x).symm,
      with_likelihood h.a_pos h.d_pos]
  have hh' := likelihood_deriv (a:=R a) (d:=R d) h.target h.reference
  have hr := Measure.rnDeriv_withDensity ν hf.ennreal_ofReal
  rw [hh] at hr
  have hz : ∀ᵐ y ∂ν, f y = likelihood S (R a) T (R d) y := by
    filter_upwards [hh',hr] with y h1 h2
    have hi := congr_arg ENNReal.toReal (h2.symm.trans h1)
    simpa only [ENNReal.toReal_ofReal (hg _), ENNReal.toReal_ofReal (like_pos h.target h.reference _ _ _).le] using hi
  rw [he]
  exact h.dest.quasiMeasurePreserving.tendsto_ae.eventually hz

/-- Every p, even before determining if the prices are finite. -/
theorem lower (p : ℝ) :
    (Integrable (fun x => likelihood A a D d x ^ p) (shift D d) ↔
      Integrable (fun y => likelihood S (R a) T (R d) y ^ p) (shift T (R d))) ∧
    (∫ x, likelihood A a D d x ^ p ∂shift D d) = ∫ y,likelihood S (R a) T (R d) y ^ p ∂shift T (R d) := by
  let f := fun y => likelihood S (R a) T (R d) y ^ p
  have hr : (fun x => likelihood A a D d x ^ p)=ᵐ[shift D d] (fun x => f (R x)) := h.read.mono fun x he => congr_arg (· ^ p) he
  rw [integrable_congr hr,integral_congr_ae hr]
  exact pay_pull h.dest f ((like_meas ..).pow measurable_const).aestronglyMeasurable

lemma integrable_iff (p : ℝ) :
    Integrable (fun x => likelihood A a D d x ^ p) (shift D d) ↔ (mixed S T p).PosDef :=
  (h.lower p).1.trans (like_integrable_iff h.target h.reference)

theorem spectral_iff (p : ℝ) : (mixed A D p).PosDef ↔ (mixed S T p).PosDef :=
  (like_integrable_iff (a:=a) (d:=d) h.a_pos h.d_pos).symm.trans (h.integrable_iff p)



-- not borrowing the ambient price in trading off normalization, true exact local cost
lemma integral_eq {p : ℝ} (hp : (mixed S T p).PosDef) :
    (∫ x, likelihood A a D d x ^ p ∂shift D d)=price S T p (R d-R a) :=
  (h.lower _).2.trans (like_integral h.target h.reference hp)
lemma price_eq {p : ℝ} (hp : (mixed S T p).PosDef) : price A D p (d-a)=price S T p (R d-R a) :=
  (like_integral h.a_pos h.d_pos ((h.spectral_iff p).mpr hp)).symm.trans (h.integral_eq hp)


end Sufficient





end reduction
end YM.SectorTools.PhysicalGaussianSwitch
