import Mathlib.Analysis.PSeries
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Resolvent
import YM.Next.EXTRACTION.Tails
import YM.Next.FREE_KERNELS.Moderate
import YM.Push.FREE_RESOLVENT.Differentiated
import YM.Work.C13.Decay
import YM.Work.G07.Calculus




/-!
# Meeting a smooth germ along a compact shift

This layer is qualitative (NO uniformity assumptions/prices on the size
of neighborhoods, we use only ambient smoothness at the given point). We will
be careful to parameterize even the *tail* integrals on a compact interval
so real germs through at most k derivatives make sense despite the absence
of sector validity on neighborhoods. Use ordinary coordinates in left patches;
no-step derivatives inferred from passage through changing masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Function Set Filter MeasureTheory FreeResolvent TestD
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {τ : Type*}

namespace Ink

abbrev interval := Icc (0:ℝ) 1

omit [NormedSpace ℝ E] in
lemma onward {r : E × ℝ → Prop} {x : E} (h : ∀ t∈ interval, ∀ᶠ p in 𝓝 (x,t), r p) : ∀ᶠ y in 𝓝 x,∀ t∈interval,r (y,t) := by
  obtain ⟨u,v,hu,-,hx,hv,hp⟩ := generalized_tube_lemma (isCompact_singleton (x:=x)) (s:={x}) (show IsCompact interval from isCompact_Icc)
    (isOpen_interior (s:={p| r p})) (show {x} ×ˢ interval ⊆ interior {p | r p} from by
      rintro ⟨z,t⟩ ⟨(he : z∈({x}:Set E)),ht⟩; replace he := mem_singleton_iff.mp he; rw [he]; exact mem_interior_iff_mem_nhds.mpr (h t ht))
  filter_upwards [hu.mem_nhds (hx (mem_singleton _))] with y hy using fun t ht => interior_subset (hp (show (y,t)∈u×ˢv from ⟨hy,hv ht⟩))

section integral
variable {g : E × ℝ→ F} {k : ℕ} {x : E}

def Arc (g : E × ℝ → F) (k : ℕ) (x : E) := ∀ t∈interval, ContDiffAt ℝ k g (x,t)

lemma Arc.persists (h : Arc g k x) : ∀ᶠ y in 𝓝 x, Arc g k y := onward (fun t ht => (h t ht).eventually (by simp))
lemma Arc.slice (h : Arc g k x) : ContinuousOn (fun t => g (x,t)) interval := fun t ht =>
  ((h t ht).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
lemma Arc.int (h : Arc g k x) : IntegrableOn (fun t=>g (x,t)) interval := h.slice.integrableOn_Icc

lemma offset {f : E × ℝ→ F} {t : ℝ} (h : ContDiffAt ℝ k f (x,t)) : ContDiffAt ℝ k (fun y => f (y,t)) x :=
  h.comp x ((contDiff_id.prodMk contDiff_const).contDiffAt)

def margin (g : E × ℝ → F) (p : E × ℝ) := fderiv ℝ (fun x => g (x,p.2)) p.1

lemma margin_smooth {t : ℝ} (h : ContDiffAt ℝ (↑(k+1:ℕ):ℕ∞ω) g (x,t)) : ContDiffAt ℝ k (margin g) (x,t) :=
  ContDiffAt.fderiv (f:=fun (p : E × ℝ) (x : E) => g (x,p.2)) (g:=Prod.fst)
    (h.comp (f:=fun p : (E × ℝ) × E => (p.2,p.1.2)) ((x,t),x) ((contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)).contDiffAt)) contDiffAt_fst (by simp)

lemma Arc.margins (h : Arc g (k+1) x) : Arc (margin g) k x := fun t ht => margin_smooth (h t ht)

variable [FiniteDimensional ℝ E]

lemma Arc.cont (h : Arc g k x) : ContinuousAt (fun y => ∫ t in interval,g (y,t)) x := by
  obtain ⟨a,ha,hp⟩ := Metric.mem_nhds_iff.mp h.persists
  have hx : 0<a/2 := half_pos ha
  let B := Metric.closedBall x (a/2)
  have ht (y : E) (hy : y∈B) : Arc g k y := hp ((Metric.closedBall_subset_ball (half_lt_self ha)) hy)
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x (a/2)).prod (show IsCompact interval from isCompact_Icc)).exists_bound_of_continuousOn (show ContinuousOn g (B ×ˢ interval) from
    fun ⟨y,t⟩ hy => (ht y hy.1 t hy.2).continuousAt.continuousWithinAt)
  refine continuousAt_of_dominated (bound:=fun _ : ℝ => C) (h.persists.mono fun x he => (Arc.int he).aestronglyMeasurable) ?_ (integrable_const _) ?_
  · filter_upwards [Metric.closedBall_mem_nhds x hx] with y hy
    exact (ae_restrict_mem measurableSet_Icc).mono fun z (hz : z∈interval) => hC (y,z) ⟨hy,hz⟩
  exact (ae_restrict_mem measurableSet_Icc).mono fun t (ht : t∈interval) => (offset (h t ht)).continuousAt

variable [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
lemma Arc.move (h : Arc g (k+1) x) : HasFDerivAt (fun y => ∫ t in interval,g (y,t)) (∫ t in interval, margin g (x,t)) x := by
  obtain ⟨a,ha,hp⟩ := Metric.mem_nhds_iff.mp h.persists
  have hx : 0<a/2 := half_pos ha
  let B := Metric.closedBall x (a/2)
  have ht (y : E) (hy : y∈B) : Arc g (k+1) y := hp ((Metric.closedBall_subset_ball (half_lt_self ha)) hy)
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x (a/2)).prod (show IsCompact interval from isCompact_Icc)).exists_bound_of_continuousOn
      (show ContinuousOn (margin g) (B ×ˢ interval) from fun ⟨y,t⟩ hy =>
        ((ht y hy.1).margins t hy.2).continuousAt.continuousWithinAt)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound:=fun _ : ℝ => C) (F' := fun y t => margin g (y,t))
    (Metric.closedBall_mem_nhds x hx) (h.persists.mono fun _ he => (Arc.int he).aestronglyMeasurable) h.int h.margins.int.aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Icc).mono fun t (hz : t∈interval) y hy => hC (y,t) ⟨hy,hz⟩) (integrable_const _)
  exact (ae_restrict_mem measurableSet_Icc).mono fun t (hz : t∈interval) y hy =>
    ((offset (ht y hy t hz)).differentiableAt (by simp)).hasFDerivAt

lemma Arc.writes (h : Arc g k x) : ContDiffAt ℝ k (fun y => ∫ t in interval,g (y,t)) x := by
  induction k generalizing F with
  | zero => exact contDiffAt_zero.mpr ⟨{y|Arc g 0 y},h.persists,fun y hy => (Arc.cont hy).continuousWithinAt⟩
  | succ k ih => rw [Nat.cast_add,Nat.cast_one,contDiffAt_succ_iff_hasFDerivAt]; exact
      ⟨fun y => ∫ t in interval,margin g (y,t), ⟨{y| Arc g (k+1) y},h.persists,fun y (hy : Arc g (k+1) y) => hy.move⟩,ih h.margins⟩

variable (v : τ → E)

def over (g : E × ℝ → F) (j : List τ) (p : E × ℝ) := TestD.jet v (fun x => g (x,p.2)) j p.1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma over_smooth {t : ℝ} (j : List τ) (h : ContDiffAt ℝ (↑(k+j.length):ℕ∞ω) g (x,t)) : ContDiffAt ℝ k (over v g j) (x,t) := by
  induction j generalizing x t k with
  | nil => unfold over; simp_rw [zeroth]; simpa using h
  | cons a l ih =>
    rw [show k+(a::l).length=k+1+l.length by simp; omega] at h
    refine ((margin_smooth (ih h)).clm_apply (g:=fun _ => v a) contDiffAt_const).congr_of_eventuallyEq ?_
    have hv (n : ℕ) : (n:ℕ∞ω) ≠ ∞ := by simp
    filter_upwards [h.eventually (hv _)] with ⟨y,z⟩ hy
    exact jet_step v _ _ (offset (smooth_of_le hy (by omega)))

lemma Arc.report (j : List τ) (h : Arc g j.length x) :
    TestD.jet v (fun y => ∫ t in interval,g (y,t)) j x = ∫ t in interval, over v g j (x,t) := by
  induction j generalizing x with
  | nil => unfold over; simp_rw [zeroth]
  | cons a l ih =>
    have hm : Arc (over v g l) (0+1) x := fun t ht => over_smooth v _ (by simpa [add_comm] using (h t ht))
    rw [jet_step v _ _ h.writes]
    have he : TestD.jet v (fun y => ∫ t in interval,g (y,t)) l =ᶠ[𝓝 x] fun y => ∫ t in interval,over v g l (y,t) := by
      filter_upwards [h.persists] with y hy using ih (fun t ht => smooth_of_le (hy t ht) (by simp))
    rw [he.fderiv_eq,hm.move.fderiv]
    rw [ContinuousLinearMap.integral_apply (𝕜:=ℝ) hm.margins.int]
    exact setIntegral_congr_fun measurableSet_Icc fun t ht => (jet_step v a l (offset (h t ht))).symm
end integral

section scaling

lemma atten_image : attenuation '' Ioi 0 = Ioo 0 1 := by
  ext t; constructor
  · rintro ⟨x,h,rfl⟩
    refine ⟨attenuation_pos h.out.le,?_⟩
    have hx := h.out
    exact inv_lt_one_of_one_lt₀ (by linarith)
  intro ⟨ht,h⟩; refine ⟨t⁻¹-1,?_,?_⟩
  · rw [mem_Ioi]; apply sub_pos.mpr; exact (one_lt_inv₀ ht).mpr h
  unfold attenuation; rw [show 1+(t⁻¹-1) = t⁻¹ from by ring,inv_inv]
private lemma atten_j : Set.InjOn attenuation (Ioi 0) := fun x hx y hy he => by simpa only [attenuation, inv_inj,add_right_inj] using he
private lemma atten_der (u : ℝ) (hu : u ∈ Ioi 0) : HasDerivWithinAt attenuation (- attenuation u^2) (Ioi 0) u := by
  have hx := hu.out
  have he := ((hasDerivAt_id' u).const_add 1).inv (show 1+u ≠ 0 from ne_of_gt (by linarith))
  simpa only [attenuation,inv_pow,one_div,neg_div] using! he.hasDerivWithinAt

lemma panel_integral (f : ℝ → F) : (∫ t in interval, f t) = ∫ u in Ioi 0, attenuation u^2 • f (attenuation u) := by
  rw [integral_Icc_eq_integral_Ioo,← atten_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi atten_der atten_j f]
  simp_rw [abs_neg,abs_of_nonneg (sq_nonneg (attenuation _))]
lemma panel_int {f : ℝ→ F} (h : IntegrableOn f interval) : IntegrableOn (fun u : ℝ => attenuation u^2 • f (attenuation u)) (Ioi 0) := by
  have hf : IntegrableOn f (attenuation '' Ioi 0) := by rw [atten_image]; exact h.mono_set Ioo_subset_Icc_self
  have hh := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi atten_der atten_j f).mp hf
  simp_rw [abs_neg,abs_of_nonneg (sq_nonneg (attenuation _))] at hh; exact hh

lemma jet_const_smul {f : E→F} (v : τ→E) (j : List τ) {x : E} (c : ℝ) (h : ContDiffAt ℝ j.length f x) :
    jet v (fun y => c • f y) j x = c • jet v f j x := jet_linear v _ (c • ContinuousLinearMap.id ℝ F) h

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {g : E × ℝ → F} {f : E → ℝ → F} {x : E} {k : ℕ}

/-- Price-independent language for the *actual* markings at a point,
including IntegrableOn of differentiated label arcs. hV on the WHOLE common
letter at y, holding geometry (including both W and F, all tags) fixed. -/
lemma panel_report (h : Arc g k x) (hV : ∀ᶠ y in 𝓝 x, ∀ u∈Ioi (0:ℝ), f y u=attenuation u^2 • g (y,attenuation u)) (v : τ→E) :
    let r := fun y => ∫ u in Ioi 0,f y u
    ContDiffAt ℝ k r x ∧ ∀ j : List τ, j.length ≤ k →
      let F u := jet v (fun y => f y u) j x
      IntegrableOn F (Ioi 0) ∧ jet v r j x=∫ u in Ioi 0, F u := by
  intro r
  have hh : r =ᶠ[𝓝 x] fun y => ∫ t in interval, g (y,t) := by
    filter_upwards [hV] with y hy
    unfold r; rw [panel_integral]; exact setIntegral_congr_fun measurableSet_Ioi hy
  refine ⟨h.writes.congr_of_eventuallyEq hh,?_⟩
  intro j hj F
  have hx : Arc g j.length x := fun t ht => smooth_of_le (h t ht) hj
  let T (t : ℝ) := over v g j (x,t)
  have hp : EqOn (fun u => attenuation u^2 • T (attenuation u)) F (Ioi 0) := by
    intro u hu
    unfold F
    rw [identical v (B:=fun y => attenuation u^2 • g (y,attenuation u)) (hV.mono fun _ hy => hy _ hu) j,
      jet_const_smul v j _ (offset (hx (attenuation u) ⟨(attenuation_pos hu.out.le).le, attenuation_le hu.out.le⟩))]; rfl
  have hi : Arc (over v g j) 0 x := fun t ht => over_smooth v j (by simpa using hx t ht)
  refine ⟨(panel_int (show IntegrableOn T interval from hi.int)).congr_fun hp measurableSet_Ioi,?_⟩
  rw [identical v hh,hx.report,panel_integral]; exact setIntegral_congr_fun measurableSet_Ioi hp
end scaling
end Ink
end YM.AnalyticBridge.RelativeLogdet
