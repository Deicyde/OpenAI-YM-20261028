import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Compactification.OnePoint.Basic
import YM.Distribution.Tests
import YM.Heat.Rows
/-! # Reverse moment estimate from character functions: a finite-difference argument.

Plane waves in radians. Both time independent (spec measure finite).
-/
noncomputable section
namespace YM.Outer.Dif
open Function Set Filter MeasureTheory Complex Boundary Probe
open scoped Topology InnerProductSpace ContDiff NNReal ENNReal BigOperators ComplexConjugate

private def diff (h s : ℝ) (f : ℝ → ℂ) (t : ℝ) := h⁻¹ • (f (t+s) - f t)
private def pair (h : ℝ) (k : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  match k with
  | 0 => f
  | k+1 => pair h k (diff h (-h) (diff h h f))
private lemma d_sm (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (s h) : ContDiff ℝ ∞ (diff h s f) := by
  unfold diff; fun_prop

private lemma one_less (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (C : ℝ) (hC : ∀ x, ‖iteratedDeriv (n+1) f x‖ ≤ C)
    (h s : ℝ) (hh : 0<h) (hs : ‖s‖=h) (x : ℝ) : ‖iteratedDeriv n (diff h s f) x‖ ≤ C := by
  unfold diff
  have hz : ContDiff ℝ n (fun t : ℝ => f (t+s)) := by
    exact (hf.of_le (m:=↑n) (by exact_mod_cast le_top)).comp (f:=fun t : ℝ => t+s) (by fun_prop)
  have hhf : ContDiff ℝ n f := hf.of_le (by exact_mod_cast le_top)
  rw [iteratedDeriv_fun_const_smul_field,iteratedDeriv_fun_sub hz.contDiffAt hhf.contDiffAt,
    iteratedDeriv_comp_add_const,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh)]
  have he := Convex.norm_image_sub_le_of_norm_deriv_le (C:=C) (x:=x) (y:=x+s) (s:=univ)
    (f:=iteratedDeriv n f)
    (fun x _ => hf.differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n) x)
    (fun x _ => by rw [← iteratedDeriv_succ]; exact hC x) convex_univ (mem_univ _) (mem_univ _)
  rw [add_sub_cancel_left,hs] at he
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left he (inv_pos.mpr hh).le
    _ = C := by field_simp

private lemma keeps (k) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (C : ℝ) (hC : ∀ x, ‖iteratedDeriv (2*k) f x‖ ≤ C)
    (h : ℝ) (hh : 0<h) (x : ℝ) : ‖pair h k f x‖ ≤ C := by
  induction k generalizing f with
  | zero => simpa [pair] using hC x
  | succ k ih =>
    refine ih _ (d_sm _ (d_sm _ hf h h) _ _) ?_
    exact one_less _ (d_sm _ hf h h) (2*k) C (one_less _ hf (2*k+1) C (by
      rw [show 2*k+1+1=2*(k+1) by omega]; exact hC) h h hh (by simp [abs_of_pos hh])) h (-h) hh (by simp [abs_of_pos hh])

section
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (p : X → ℝ)
private def tilt (h s : ℝ) x := h⁻¹ • (plane (p x) s - 1)
private def wt (h : ℝ) x := ‖tilt p h h x‖^2
private def ft (g : X→ℂ) (t : ℝ) := ∫ x, plane (p x) t * g x ∂μ

omit [MeasurableSpace X] in
private lemma flipped (h : ℝ) x : tilt p h (-h) x=star (tilt p h h x) := by
  simp [tilt,plane_inverse]
private lemma turns (hp : Measurable p) (h s) (g : X → ℂ) (hg : Integrable g μ) :
    Integrable (fun x => tilt p h s x * g x) μ := by
  apply hg.bdd_mul (c:= ‖h⁻¹‖*(1+1:ℝ))
  · unfold tilt plane; fun_prop
  filter_upwards with x
  rw [tilt,norm_smul]; gcongr
  simpa using norm_sub_le (plane (p x) s) 1

private lemma df (hp : Measurable p) (h s) (g : X → ℂ) (hg : Integrable g μ) :
    diff h s (ft μ p g)=ft μ p (fun x => tilt p h s x * g x) := by
  have hv (r : ℝ) : Integrable (fun x => plane (p x) r * g x) μ := by
    apply hg.bdd_mul (c:=1)
    · unfold plane; fun_prop
    · filter_upwards with x; simp
  funext t
  unfold diff ft
  rw [← integral_sub (hv _) (hv _),← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only; rw [plane_add]; unfold tilt
  simp only [Complex.real_smul]; ring

private lemma toPair (hp : Measurable p) (h : ℝ) (k) (g : X → ℂ) (hg : Integrable g μ) :
    let b := fun x => ↑(wt p h x ^ k)*g x
    Integrable b μ ∧ pair h k (ft μ p g)=ft μ p b := by
  induction k generalizing g with
  | zero => simp only [pow_zero,ofReal_one,one_mul, pair]; exact ⟨hg,trivial⟩
  | succ k ih =>
    simp only [pair]
    have hi := turns μ p hp h h g hg
    let G := fun x => tilt p h (-h) x * (tilt p h h x * g x)
    have hj : Integrable G μ := turns μ p hp h (-h) _ hi
    have he : (fun x => ↑(wt p h x ^ k)*G x) = fun x => ↑(wt p h x ^ (k+1))*g x := by
      funext x
      dsimp only [G]
      have hh : tilt p h (-h) x * tilt p h h x=↑(wt p h x) := by
        rw [flipped,mul_comm]; exact (mul_conj _).trans (by simp [wt,normSq_eq_norm_sq])
      rw [← mul_assoc (tilt p h (-h) x),hh,pow_succ,ofReal_mul,mul_assoc]
    rw [df μ p hp _ _ _ hg,df μ p hp _ _ _ hi,← he]
    exact ih G hj
end

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (p : X → ℝ) (hp : Measurable p)

include hp
/-- Derivative cap implies the coordinate moment bound, without assuming spectral domain
regularity of any vector. -/
lemma estimate (k : ℕ) (C : ℝ) (hc : 0 ≤ C) (F : ℝ → ℂ) (hr : ∀ t, F t=∫ x, plane (p x) t ∂μ)
    (hf : ContDiff ℝ ∞ F) (hs : ∀ x, ‖iteratedDeriv (2*k) F x‖ ≤ C) :
    Integrable (fun x => ‖p x‖ ^ (2*k)) μ ∧ (∫ x, ‖p x‖ ^ (2*k) ∂μ) ≤ C := by
  let w := fun (h : ℝ) x => wt p h x ^ k
  have hw (x : X) (h : ℝ) : 0 ≤ w h x := by unfold w wt; positivity
  have hu (h : ℝ) (hh : 0<h) : ∫⁻ x, ‖w h x‖ₑ ∂μ ≤ ENNReal.ofReal C := by
    have hb := toPair μ p hp h k (fun _ => 1) (integrable_const _)
    simp only [mul_one] at hb
    have hv : Integrable (fun x => (↑(w h x) : ℂ)) μ := hb.1
    have hz : ft μ p (fun _ => 1)=F := by
      funext t; simp [ft,hr]
    have hi := congr_fun hb.2 0
    rw [hz] at hi
    unfold ft at hi; simp_rw [plane_zero,one_mul] at hi
    change _= ∫ x, (↑(w h x):ℂ) ∂μ at hi
    rw [integral_complex_ofReal] at hi
    have he := keeps k F hf C hs h hh 0; rw [hi] at he
    simp only [Complex.norm_real,Real.norm_eq_abs] at he
    have hx : Integrable (w h) μ := by simpa using hv.re
    rw [← ofReal_integral_norm_eq_lintegral_enorm hx,show (fun x => ‖w h x‖) = w h from funext fun x => by simp [abs_of_nonneg (hw x h)]]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans he)
  let l := 𝓝[>] (0:ℝ)
  have he (x : X) : Tendsto (fun h => ‖w h x‖ₑ) l (𝓝 ‖‖p x‖^(2*k)‖ₑ) := by
    have hy : HasDerivAt (plane (p x)) ((p x:ℝ)*I) (0:ℝ) := by
      have hx := (((hasDerivAt_id' (0:ℝ)).ofReal_comp).const_mul ((p x:ℝ):ℂ) |>.mul_const I).cexp
      change HasDerivAt (fun t : ℝ => cexp (↑(inner ℝ (p x) t) * I)) _ _
      simpa [RCLike.inner_apply,mul_comm] using hx
    have hz : Tendsto (fun h => tilt p h h x) l (𝓝 ((p x:ℝ)*I)) := by
      refine Tendsto.congr' ?_ (hy.tendsto_slope_zero.mono_left ?_)
      · exact Eventually.of_forall fun a => by simp [tilt]
      · apply nhdsWithin_mono _
        intro a ha; exact (show 0<a from ha).ne'
    have hb := (hz.norm.pow 2 |>.pow k).enorm
    simpa only [w,wt,pow_mul,norm_mul,Complex.norm_real,norm_I,mul_one] using hb
  let b : X → ℝ := fun x => ‖p x‖^(2*k)
  have ht : ∫⁻ x, ‖b x‖ₑ ∂μ ≤ ENNReal.ofReal C := calc
    _ = ∫⁻ x, liminf (fun h => ‖w h x‖ₑ) l ∂μ := lintegral_congr (fun x => (he x).liminf_eq.symm)
    _ ≤ liminf (fun h => ∫⁻ x, ‖w h x‖ₑ ∂μ) l := by
      apply lintegral_liminf_le
      intro h; unfold w wt tilt plane; fun_prop
    _ ≤ _ := liminf_le_of_frequently_le' (show ∀ᶠ h in l, _ from (show ∀ᶠ h in l, 0<h from self_mem_nhdsWithin).mono fun _ => hu _).frequently
  have hb : Integrable b μ := ⟨by unfold b;fun_prop, lt_of_le_of_lt ht ENNReal.ofReal_lt_top⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm hb, show (fun x => ‖b x‖)=b from funext fun x => abs_of_nonneg (by unfold b; positivity)] at ht
  exact ⟨hb,(ENNReal.ofReal_le_ofReal_iff hc).mp ht⟩
end YM.Outer.Dif
