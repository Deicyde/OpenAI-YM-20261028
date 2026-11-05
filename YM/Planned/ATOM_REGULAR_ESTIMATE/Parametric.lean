import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.OS.Halves
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15


/-! Ordinary finite-order regularity and domination at the integral interface.
No uniform numerical bounds in these assumptions; in particular, any dominating
function cost here may grow with the torus. Differentiation of a component uses
a COMMON local pre-mask integral continuation including at equality. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators

section
variable {Z : Type*} {E F : Type} [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def average (μ : Measure Z) (f : Z → E → F) : E → F := fun x => ∫ z, f z x ∂μ

structure Under (μ : Measure Z) (f : Z → E → F) (n : ℕ) (s : Set E) (b : Z → ℝ) : Prop where
  regular : ∀ᵐ z ∂μ, ∀ y∈s, ContDiffAt ℝ n (f z) y
  measurable (i : ℕ) : i ≤ n → ∀ y∈s, AEStronglyMeasurable (fun z => iteratedFDeriv ℝ i (f z) y) μ
  cost : Integrable b μ
  uniform : ∀ᵐ z ∂μ, ∀ y∈s, ∀ i ≤ n, ‖iteratedFDeriv ℝ i (f z) y‖ ≤ b z

def Covered (μ : Measure Z) (f : Z → E → F) (n : ℕ) (x : E) : Prop :=
  ∃ s, IsOpen s ∧ x∈s ∧ ∃ b, Under μ f n s b

variable {μ : Measure Z} {f : Z → E → F} {n : ℕ} {x : E} {s : Set E} {b : Z → ℝ}

namespace Under

lemma integrate (h : Under μ f n s b) (hx : x∈s) {k : ℕ} (hk : k ≤ n) :
    Integrable (fun z => iteratedFDeriv ℝ k (f z) x) μ := h.cost.mono' (h.measurable k hk _ hx)
      (h.uniform.mono fun _ hz => hz x hx k hk)

lemma observe (h : Under μ f n s b) (hx : x∈s) : Integrable (fun z => f z x) μ := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) F 0
  have he := L.integrable_comp (h.integrate hx (Nat.zero_le n))
  simpa only [L,ContinuousMultilinearMap.apply_apply,iteratedFDeriv_zero_apply] using he

lemma through (h : Under μ f (n+1) s b) : Under μ (fun z => fderiv ℝ (f z)) n s b := by
  refine ⟨h.regular.mono (fun z hz y hy => (hz y hy).fderiv_right (by push_cast; rfl)),
    fun i hi y hy => ?_,h.cost,h.uniform.mono (fun z hz y hy i hi => ?_)⟩
  · let L := continuousMultilinearCurryRightEquiv' ℝ i E F
    have ht := L.continuous.comp_aestronglyMeasurable (h.measurable (i+1) (by omega) y hy)
    simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, L, LinearIsometryEquiv.apply_symm_apply] using ht
  simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_def,LinearIsometryEquiv.norm_map] using hz y hy (i+1) (by omega)

lemma continuous (h : Under μ f n s b) (hs : IsOpen s) (hx : x∈s) : ContinuousAt (average μ f) x :=
  continuousAt_of_dominated (F:=fun y z => f z y) ((show ∀ᶠ y in 𝓝 x,y ∈ s from hs.mem_nhds hx).mono (fun y hy => (h.observe hy).aestronglyMeasurable))
    ((show ∀ᶠ y in 𝓝 x,y ∈ s from hs.mem_nhds hx).mono (fun y hy => h.uniform.mono fun z hz => by simpa using hz y hy 0 (Nat.zero_le _)))
    h.cost (h.regular.mono fun z hz => (hz x hx).continuousAt)

lemma deriv (h : Under μ f (n+1) s b) (hs : IsOpen s) (hx : x∈s) :
    HasFDerivAt (average μ f) (average μ (fun z => fderiv ℝ (f z)) x) x :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le (F:=fun y z => f z y) (F':=fun y z => fderiv ℝ (f z) y)
    (hs.mem_nhds hx)
    ((show ∀ᶠ y in 𝓝 x,y ∈ s from hs.mem_nhds hx).mono (fun y hy => (h.observe hy).aestronglyMeasurable))
    (h.observe hx) (h.through.observe hx).aestronglyMeasurable
    (h.through.uniform.mono fun z hz y hy => by simpa using hz y hy 0 (Nat.zero_le _))
    h.cost (h.regular.mono (fun z hz y hy => ((hz y hy).differentiableAt (by push_cast; simp)).hasFDerivAt))

lemma less (h : Under μ f n s b) {k : ℕ} (hk : k ≤ n) : Under μ f k s b :=
  ⟨h.regular.mono (fun _ hz y hy => (hz y hy).of_le (Nat.cast_le.mpr hk)),fun i hi => h.measurable i (hi.trans hk),
    h.cost,h.uniform.mono fun _ hz y hy i hi => hz y hy i (hi.trans hk)⟩

lemma germ (h : Under μ f n s b) (hs : IsOpen s) (hx : x∈s) : ContDiffAt ℝ n (average μ f) x := by
  induction n generalizing F with
  | zero => simpa only [Nat.cast_zero,contDiffAt_zero] using!
      (show ∃ u∈ 𝓝 x, ContinuousOn (average μ f) u from ⟨s,hs.mem_nhds hx,fun y hy => (h.continuous hs hy).continuousWithinAt⟩)
  | succ n ih =>
    push_cast; rw [contDiffAt_succ_iff_hasFDerivAt]
    exact ⟨average μ (fun z => fderiv ℝ (f z)),⟨s,hs.mem_nhds hx,fun y hy => h.deriv hs hy⟩,ih h.through⟩

lemma differentiate [CompleteSpace F] (h : Under μ f n s b) (hs : IsOpen s) (hx : x∈s) :
    iteratedFDeriv ℝ n (average μ f) x = ∫ z, iteratedFDeriv ℝ n (f z) x ∂μ := by
  induction n generalizing F with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    simp_rw [iteratedFDeriv_zero_eq_comp]; exact (L.integral_comp_comm (h.observe hx)).symm
  | succ n ih =>
    let L := (continuousMultilinearCurryRightEquiv' ℝ n E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have he := L.integral_comp_comm (h.through.integrate hx (le_refl n))
    have hu : fderiv ℝ (average μ f) =ᶠ[𝓝 x] average μ (fun z => fderiv ℝ (f z)) :=
      (show ∀ᶠ y in 𝓝 x,y ∈ s from hs.mem_nhds hx).mono fun y hy => (h.deriv hs hy).fderiv
    simp_rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply]
    rw [(hu.iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds, ih h.through]
    exact he.symm
end Under

namespace Covered

lemma ae (h : Covered μ f n x) : ∀ᵐ z ∂μ, ContDiffAt ℝ n (f z) x := by
  obtain ⟨s,-,hx,b,h⟩ := h; exact h.regular.mono fun z hz => hz x hx

lemma leaves (h : Covered μ f n x) {F' : E → F} (hF : F' =ᶠ[𝓝 x] average μ f) : ContDiffAt ℝ n F' x := by
  obtain ⟨s,hs,hx,b,h⟩ := h; exact (h.germ hs hx).congr_of_eventuallyEq hF

/-- Every `C^n` change/testing of parameters may read from the SAME integral.
No extra assumption about interchanging an ordered derivative. -/
lemma test {J : Type} [NormedAddCommGroup J] [NormedSpace ℝ J] [CompleteSpace F]
    {Φ : J → E} {a : J} (h : Covered μ f n (Φ a)) {F' : E → F} (hF : F' =ᶠ[𝓝 (Φ a)] average μ f)
    (hΦ : ContDiffAt ℝ n Φ a) {k : ℕ} (hk : k ≤ n) (v : Fin k → J) :
    Integrable (fun z => iteratedFDeriv ℝ k (f z ∘ Φ) a v) μ ∧
      iteratedFDeriv ℝ k (F' ∘ Φ) a v = ∫ z, iteratedFDeriv ℝ k (f z ∘ Φ) a v ∂μ := by
  have hx (p : E → F) (hp : ContDiffAt ℝ n p (Φ a)) :
      iteratedFDeriv ℝ k (p ∘ Φ) a v = ∑ q : OrderedFinpartition k,
        iteratedFDeriv ℝ q.length p (Φ a) (fun i => iteratedFDeriv ℝ (q.partSize i) Φ a (fun j => v (q.emb i j))) := by
    rw [iteratedFDeriv_comp hp hΦ (Nat.cast_le.mpr hk), FormalMultilinearSeries.taylorComp, sum_apply]
    rfl
  obtain ⟨s,hs,hy,b,u⟩ := h
  let P (q : OrderedFinpartition k) := ContinuousMultilinearMap.apply ℝ (fun _ : Fin q.length => E) F
    (fun i => iteratedFDeriv ℝ (q.partSize i) Φ a (fun j => v (q.emb i j)))
  have he (q : OrderedFinpartition k) : Integrable (fun z => P q (iteratedFDeriv ℝ q.length (f z) (Φ a))) μ :=
    (P q).integrable_comp (u.integrate hy (q.length_le.trans hk))
  have ht : (fun z => iteratedFDeriv ℝ k (f z ∘ Φ) a v) =ᵐ[μ]
      fun z => ∑ q : OrderedFinpartition k, P q (iteratedFDeriv ℝ q.length (f z) (Φ a)) :=
    u.regular.mono fun z hz => hx (f z) (hz (Φ a) hy)
  refine ⟨(integrable_finsetSum _ (fun q _ => he q)).congr ht.symm,?_⟩
  rw [hx F' ((u.germ hs hy).congr_of_eventuallyEq hF), integral_congr_ae ht, integral_finsetSum _ (fun q _ => he q)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [(hF.iteratedFDeriv (𝕜:=ℝ) q.length).eq_of_nhds, (u.less (q.length_le.trans hk)).differentiate hs hy]
  exact Eq.symm ((P q).integral_comp_comm (u.integrate hy (q.length_le.trans hk)))
end Covered
end
end YM.Planned.AtomRegular
