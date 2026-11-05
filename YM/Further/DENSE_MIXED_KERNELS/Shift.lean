import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Analysis.Polydisc
import YM.Bid.Fuels
import YM.Further.DENSE_MIXED_KERNELS.Window
import YM.Org.Theatre
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15


/-!
# Local parametric integration with genuine ordered left derivatives
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Lattice RG Wilson
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {n : Side} {k j : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "I" => Directions G n

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- C^k integral-exchange hypothesis BEFORE the locality indicator.
Existence of a domination on the germ only (can depend on the period,
location in the cut, alphabet, etc.). Costs used separately. -/
def Varies (μ : Measure Ω) (k : ℕ) (U : Config G n) (f : Ω → Config G n → E) :=
  Window μ k 0 (fun i => f i ∘ increment U)

variable {U : Config G n} {f : Ω → Config G n → E}

def Rests (g : Config G n → E) (k : ℕ) (U : Config G n) :=
  ContDiffAt ℝ k (g ∘ increment U) 0

-- around (moving point, displacement), use *single* neighborhood of identity.
-- No need for a Healthy assumption in this change of derivative coordinates.
private def logShift (v : I × I) : I := fun e => G.plog (G.mat (G.lieExp (v.2 e) * G.lieExp (v.1 e)))
private lemma logShift_zero : logShift (0 : I × I)=0 := by ext1 e; simp [logShift]
private lemma logShift_diff : ContDiffAt ℝ ω (logShift (G:=G) (n:=n)) 0 := by
  refine contDiffAt_pi.mpr fun i => ?_
  let f (u : I × I) := G.mat (G.lieExp (u.2 i) * G.lieExp (u.1 i))
  have hf : ContDiffAt ℝ ω f 0 := by
    unfold f; simp only [G.mat_mul]
    apply ContDiffAt.mul
    · exact (G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp contDiff_snd)).contDiffAt
    exact (G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp contDiff_fst)).contDiffAt
  exact ContDiffAt.comp (f:=f) (g:=G.plog) _ (by simp only [show f 0=1 by simp [f]]; exact G.plog_diff) hf
private lemma folded (U : Config G n) : ∀ᶠ v : I × I in 𝓝 0,
    increment (increment U v.1) v.2=increment U (logShift v) := by
  simp only [funext_iff, eventually_all]
  intro i
  let f (v : I × I) := G.lieExp (v.2 i) * G.lieExp (v.1 i)
  have ht : Tendsto f (𝓝 0) (𝓝 1) := by
    rw [← show f 0=1 by simp [f]]; exact (show Continuous f from (by unfold f; fun_prop)).tendsto _
  filter_upwards [ht.eventually G.plog_right] with v hv
  unfold increment logShift; rw [show G.lieExp _=_ from hv, ← mul_assoc]

private lemma map_coords (A : I) (C : I → E) {T : I →L[ℝ] E} (h : HasFDerivAt C T 0) :
    HasDerivAt (fun t : ℝ => C (t • A)) (T A) 0 := by
  let f (t : ℝ) := t • A
  exact (HasFDerivAt.comp_hasDerivAt 0 (f:=f) (by rwa [show f 0=0 by simp [f]]) (show HasDerivAt f A _ by
    simpa using (hasDerivAt_id' (0:ℝ)).smul_const A))

lemma increment_zero (U : Config G n) : increment U 0=U := by ext1; simp [increment]
lemma rest_inside {g : Config G n → E} (h : Rests g k U) : ∀ᶠ v in 𝓝 (0:I), Rests g k (increment U v) := by
  have he := ContDiffAt.comp (f:=logShift (G:=G) (n:=n)) (0:I × I)
    (g:=g ∘ increment U) (by rwa [logShift_zero]) (logShift_diff.of_le le_top)
  have hu := he.congr_of_eventuallyEq (f₁:=fun v : I × I => g (increment (increment U v.1) v.2))
    ((folded U).mono (fun v hv => congr_arg g hv))
  let p (v : I) := (v,(0:I))
  have hp : ContDiff ℝ k p := contDiff_id.prodMk contDiff_const
  filter_upwards [(hp.continuous.tendsto _).eventually (hu.eventually (by simp))] with v hv
  exact hv.comp 0 (f:=fun z:I => (v,z)) (contDiffAt_const.prodMk contDiffAt_id)
lemma rest_near {g : Config G n → E} (h : Rests g k U) (A : I) : ∀ᶠ t : ℝ in 𝓝 0,
    Rests g k (increment U (t • A)) := by
  let p (t : ℝ) := t • A
  have ht : Tendsto p (𝓝 0) (𝓝 0) := by simpa only [p,zero_smul] using (show Continuous p from by unfold p; fun_prop).tendsto 0
  exact ht.eventually (rest_inside h)
lemma left_eq (l : List I) {g h : Config G n → E} (he : g ∘ increment U =ᶠ[𝓝 (0:I)] h ∘ increment U) :
    leftDerivs g l U = leftDerivs h l U := by
  induction l generalizing U with
  | nil => simpa [increment_zero,leftDerivs] using! he.self_of_nhds
  | cons a l ih =>
    simp only [leftDerivs]; apply Filter.EventuallyEq.deriv_eq
    let p (v : ℝ × I) := (v.1 • a,v.2)
    have ht : Tendsto p (𝓝 0) (𝓝 0) := by
      simpa only [show p 0=0 by simp [p,Prod.zero_eq_mk]] using (show Continuous p from by unfold p; fun_prop).tendsto 0
    have hs : ∀ᶠ v : ℝ × I in 𝓝 0, g (increment (increment U (v.1 • a)) v.2)=
        h (increment (increment U (v.1 • a)) v.2) := ht.eventually (p:=fun v : I × I => g (increment (increment U v.1) v.2)=
        h (increment (increment U v.1) v.2)) (by
      have hm : Tendsto logShift (𝓝 (0:I × I)) (𝓝 0) := by
        have h := logShift_diff (G:=G) (n:=n) |>.continuousAt.tendsto; rw [logShift_zero] at h; exact h
      filter_upwards [folded U,hm.eventually he] with v hv hx
      simpa only [hv] using! hx)
    rw [Prod.zero_eq_mk,nhds_prod_eq] at hs
    have hh := hs.curry
    filter_upwards [hh] with x hx; exact ih hx

namespace Varies

theorem smooth (h : Varies μ k U f) (i) : Rests (f i) k U := Window.smooth h i
theorem lower (h : Varies μ k U f) (hl : j ≤ k) : Varies μ j U f := Window.of_le h hl
theorem reads (h : Varies μ k U f) : Integrable (fun i => f i U) μ := by simpa [increment_zero] using! Window.reads h

lemma visits (h : Varies μ k U f) : Window μ k (0:I × I) (fun i (p : I × I) => f i (increment (increment U p.1) p.2)) :=
  let h' : Window μ k (logShift (0:I × I)) (fun i => f i ∘ increment U) := by rw [logShift_zero]; exact h
  (h'.comp (logShift_diff.of_le le_top)).eq ((folded U).mono fun _ hv i => congr_arg (f i) hv)

theorem oft (h : Varies μ k U f) : ∀ᶠ v in 𝓝 (0:I), Varies μ k (increment U v) f := by
  let p (v : I) := (v,(0:I)); have hp : Tendsto p (𝓝 0) (𝓝 0) := continuous_id.continuousAt.prodMk continuousAt_const
  filter_upwards [hp.eventually (Window.oft h.visits)] with v hv
  exact hv.comp (T:=fun x:I => (v,x)) (d:=0) (contDiffAt_const.prodMk contDiffAt_id)

theorem tilt (h : Varies μ (k+1) U f) (a : I) : Varies μ k U (fun i => leftDerivs (f i) [a]) := by
  let F (i : Ω) (v : I × I) := f i (increment (increment U v.1) v.2)
  let p (v : I) := (v,(0:I))
  have he : Window μ k 0 (fun i => fderiv ℝ (F i) ∘ p) := Window.comp (f:=fun i => fderiv ℝ (F i)) (T:=p) (d:=0) (show Window μ k _ _ from h.visits.lower)
    (show ContDiffAt ℝ k p 0 from contDiffAt_id.prodMk contDiffAt_const)
  have hp : Tendsto p (𝓝 0) (𝓝 0) := continuous_id.continuousAt.prodMk continuousAt_const
  refine (he.pad_constant (ContinuousLinearMap.apply ℝ E ((0:I),a))).eq ?_
  filter_upwards [hp.eventually h.visits.near] with v hv i
  have hs : HasFDerivAt (F i) (fderiv ℝ (F i) (p v)) (p v) := ((hv i).differentiableAt (by simp)).hasFDerivAt
  have hh : HasDerivAt (fun t : ℝ => (v,t • a)) ((0:I),a) 0 := (hasDerivAt_const _ _).prodMk (by
    simpa using (hasDerivAt_id' (0:ℝ)).smul_const a)
  exact ((show HasFDerivAt (F i) (fderiv ℝ (F i) (p v)) (v,(0:ℝ) • a) from (by simpa [p])).comp_hasDerivAt 0 hh).deriv

lemma post (h : Varies μ k U f) (l : List I) (hl : j+l.length ≤ k) : Varies μ j U (fun i => leftDerivs (f i) l) := by
  induction l generalizing j with
  | nil => exact h.lower (show j ≤ k from hl)
  | cons A l ih => exact (ih (show j+1+l.length ≤ k by simp only [List.length_cons] at hl; omega)).tilt A

lemma once (h : Varies μ (k+1) U f) (a : I) : leftDerivs (fun x => ∫ i,f i x ∂μ) [a] U = ∫ i,leftDerivs (f i) [a] U ∂μ := by
  -- apply fderiv under integral; then take requested direction
  let F (i : Ω) (v : I) := f i (increment U v)
  have hd i : HasFDerivAt (F i) (fderiv ℝ (F i) 0) 0 := ((h.smooth i : ContDiffAt ℝ (↑(k+1):WithTop ℕ∞) (F i) 0).differentiableAt (by norm_cast)).hasFDerivAt
  have hm : ∀ i,leftDerivs (f i) [a] U = (fderiv ℝ (F i) 0) a := fun i => (map_coords a (F i) (hd i)).deriv
  let f₁ (v : I) := ∫ i,F i v ∂μ
  rw [show leftDerivs _ _ U = deriv (fun t : ℝ => f₁ (t • a)) 0 from rfl,
    (map_coords a f₁ (Window.switches h)).deriv,ContinuousLinearMap.integral_apply
      (show Integrable (fun i => fderiv ℝ (F i) 0) μ from Window.reads (Window.lower h))]
  exact integral_congr_ae (Eventually.of_forall fun i => (hm i).symm)

theorem turns (h : Varies μ k U f) (l : List I) (hl : l.length ≤ k) : leftDerivs (fun x => ∫ i,f i x ∂μ) l U =
    ∫ i,leftDerivs (f i) l U ∂μ := by
  induction l generalizing U with
  | nil => rfl
  | cons a l ih =>
    have ht : Varies μ (0+1) U (fun i => leftDerivs (f i) l) := h.post l (by simp only [List.length_cons] at hl; omega)
    have he := ht.once a
    refine Eq.trans (b:=leftDerivs (fun x => ∫ i,leftDerivs (f i) l x ∂μ) [a] U) ?_ he
    change deriv _ _ = deriv _ _; apply Filter.EventuallyEq.deriv_eq
    have hv : Tendsto (fun t : ℝ => t • a) (𝓝 0) (𝓝 0) := by
      simpa only [zero_smul] using (show Continuous (fun t : ℝ => t • a) from by fun_prop).tendsto 0
    filter_upwards [hv.eventually h.oft] with t hh using ih hh (by simp only [List.length_cons] at hl; omega)

theorem integrate (h : Varies μ k U f) : Rests (fun x => ∫ i,f i x ∂μ) k U := Window.integrate h

end Varies
end YM.Further.DenseMixedKernels
