import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Taylor
import YM.PREC.Implicit
import YM.Pressure.Seeds




/-!
# Getting a Hessian from the quadratic limits on lines

Real C² germs. We won't need a remainder estimate independent of the period, or even
independent of the direction. This also lets us handle the infinite rows without needing
an identity expressing the Hessian as a sum of Hessians. Includes the pullback we're going
to use for the slice coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.F03

open Filter Function
open scoped ContDiff Topology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma value_slope_of_sq_limit {f : ℝ → ℝ} (hc : ContinuousAt f 0) {b : ℝ}
    (h : Tendsto (fun t : ℝ => f t / t ^ 2) (𝓝[≠] 0) (𝓝 b)) :
    f 0 = 0 ∧ HasDerivAt f 0 0 := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := self_mem_nhdsWithin
  have hv : Tendsto f (𝓝[≠] 0) (𝓝 0) := by
    have ha := h.mul (hid.pow 2)
    norm_num at ha
    refine ha.congr' (ne.mono fun t ht => ?_)
    exact div_mul_cancel₀ (f t) (pow_ne_zero 2 ht)
  have hz := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hv
  refine ⟨hz, hasDerivAt_iff_tendsto_slope.mpr ?_⟩
  have hd := h.mul hid
  rw [mul_zero] at hd
  refine hd.congr' (ne.mono fun t ht => ?_)
  rw [slope_def_field, hz, sub_zero, sub_zero]; field_simp

/-- At a critical point, with the value subtracted. -/
lemma taylor_limit_two {f : ℝ → ℝ} (hd : ContDiffAt ℝ 2 f 0) (hz : f 0 = 0)
    (hf : deriv f 0 = 0) :
    Tendsto (fun t : ℝ => f t / t ^ 2) (𝓝[≠] 0) (𝓝 (iteratedDeriv 2 f 0 / 2)) := by
  obtain ⟨s, hs, hu⟩ := hd.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨r, hr, hr'⟩ := Metric.mem_nhds_iff.mp hs
  let I := Metric.ball (0 : ℝ) r
  have h0 : 0 ∈ I := Metric.mem_ball_self hr
  have ht := Real.taylor_tendsto (n := 2) (convex_ball (0 : ℝ) r) h0 (hu.mono hr')
  rw [nhdsWithin_eq_nhds.mpr (Metric.isOpen_ball.mem_nhds h0)] at ht
  have he (j : ℕ) : iteratedDerivWithin j f I 0 = iteratedDeriv j f 0 :=
    iteratedDerivWithin_of_isOpen Metric.isOpen_ball h0
  have hw (x : ℝ) : taylorWithinEval f 2 I 0 x = x ^ 2 * (iteratedDeriv 2 f 0 / 2) := by
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp_rw [he]; norm_num [Nat.factorial, hf, hz]; ring
  have hh : Tendsto (fun t : ℝ => (f t - t ^ 2 * (iteratedDeriv 2 f 0 / 2)) / t ^ 2 +
        iteratedDeriv 2 f 0 / 2) (𝓝[≠] 0) (𝓝 (iteratedDeriv 2 f 0 / 2)) := by
    simpa only [I, hw, sub_zero, zero_add] using
      (ht.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).add_const (iteratedDeriv 2 f 0 / 2)
  refine hh.congr' ?_
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 from self_mem_nhdsWithin] with t ht
  field_simp; ring

lemma line_second {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hg : fderiv ℝ f 0 = 0)
    (v : E) : iteratedDeriv 2 (fun t : ℝ => f (t • v)) 0 =
      iteratedFDeriv ℝ 2 f 0 ![v,v] := by
  let l : ℝ → E := fun t => t • v
  have hl : HasDerivAt l v 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const v
  have ha : ContDiffAt ℝ 2 l 0 := by unfold l; fun_prop
  change iteratedDeriv 2 (f ∘ l) 0 = _
  rw [iteratedDeriv_vcomp_two (show ContDiffAt ℝ 2 f (l 0) by simpa [l] using hf) ha,
    hl.deriv, show l 0 = 0 by simp [l], hg]
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp

lemma hessian_symmetric {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) (v w : E) :
    iteratedFDeriv ℝ 2 f 0 ![v,w] = iteratedFDeriv ℝ 2 f 0 ![w,v] := by
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  exact hf.isSymmSndFDerivAt (by simp) v w

/-- Recover the bilinear identity from its diagonal. -/
lemma hessian_polar {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    {Q : E → E → ℝ} (hadd : ∀ x y z, Q (x+y) z = Q x z + Q y z)
    (hsym : ∀ x y, Q x y = Q y x)
    (hdiag : ∀ x, iteratedFDeriv ℝ 2 f 0 ![x,x] = Q x x) (x y : E) :
    iteratedFDeriv ℝ 2 f 0 ![x,y] = Q x y := by
  have ha : iteratedFDeriv ℝ 2 f 0 ![x+y,x+y] =
      (iteratedFDeriv ℝ 2 f 0 ![x,x] + iteratedFDeriv ℝ 2 f 0 ![x,y]) +
        (iteratedFDeriv ℝ 2 f 0 ![y,x] + iteratedFDeriv ℝ 2 f 0 ![y,y]) := by
    simp [iteratedFDeriv_two_apply]
  rw [hessian_symmetric hf y x, hdiag, hdiag, hdiag, hadd, hsym x (x+y), hsym y (x+y),
    hadd, hadd, hsym y x] at ha
  linarith

lemma hessian_of_limit {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) {Q : E → E → ℝ}
    (lim : ∀ x : E, Tendsto (fun t : ℝ => f (t • x) / t ^ 2) (𝓝[≠] 0) (𝓝 (Q x x / 2)))
    (ha : ∀ x y z, Q (x+y) z = Q x z + Q y z) (hs : ∀ x y, Q x y = Q y x) :
    f 0 = 0 ∧ fderiv ℝ f 0 = 0 ∧ ∀ x y, iteratedFDeriv ℝ 2 f 0 ![x,y] = Q x y := by
  have hd (x : E) : ContDiffAt ℝ 2 (fun t : ℝ => f (t • x)) 0 := by
    have hv : ContDiffAt ℝ 2 (fun t : ℝ => t • x) 0 := by fun_prop
    exact (show ContDiffAt ℝ 2 f ((0:ℝ) • x) by simpa using hf).comp 0 hv
  have hz (x : E) := value_slope_of_sq_limit (hd x).continuousAt (lim x)
  have hv : f 0 = 0 := by simpa using (hz 0).1
  have hg : fderiv ℝ f 0 = 0 := ContinuousLinearMap.ext (fun x =>
    (Push.side f (hf.differentiableAt (by simp)) x).unique (hz x).2)
  refine ⟨hv, hg, hessian_polar hf ha hs ?_⟩
  intro x
  have he := tendsto_nhds_unique (taylor_limit_two (hd x) (hz x).1 (hz x).2.deriv) (lim x)
  rw [line_second hf hg] at he
  linarith

/-- Pull back a Hessian when the outer gradient is zero. -/
lemma hessian_comp {f : E → ℝ} {g : F → E} (hz : g 0 = 0) (hf : ContDiffAt ℝ 2 f 0)
    (hg : ContDiffAt ℝ 2 g 0) (hv : fderiv ℝ f 0 = 0) :
    fderiv ℝ (f ∘ g) 0 = 0 ∧ ∀ x y,
      iteratedFDeriv ℝ 2 (f ∘ g) 0 ![x,y] =
        iteratedFDeriv ℝ 2 f 0 ![fderiv ℝ g 0 x, fderiv ℝ g 0 y] := by
  have hf' : ContDiffAt ℝ 2 f (g 0) := hz.symm ▸ hf
  have hcomp := hf'.comp 0 hg
  have hd : fderiv ℝ (f ∘ g) 0 = 0 := by
    rw [fderiv_comp _ (hf'.differentiableAt (by simp)) (hg.differentiableAt (by simp)), hz, hv]
    simp
  refine ⟨hd, hessian_polar hcomp (Q := fun x y =>
    iteratedFDeriv ℝ 2 f 0 ![fderiv ℝ g 0 x, fderiv ℝ g 0 y]) ?_ ?_ ?_⟩
  · intro x y z; simp [iteratedFDeriv_two_apply]
  · exact fun _ _ => hessian_symmetric hf _ _
  intro x
  rw [← line_second (f := f ∘ g) hcomp hd]
  have he : ContDiffAt ℝ 2 (fun t : ℝ => g (t • x)) 0 := by
    have hk : ContDiffAt ℝ 2 (fun t : ℝ => t • x) 0 := by fun_prop
    exact (show ContDiffAt ℝ 2 g ((0:ℝ) • x) by simpa using hg).comp 0 hk
  change iteratedDeriv 2 (f ∘ (fun t : ℝ => g (t • x))) 0 = _
  rw [iteratedDeriv_vcomp_two (by simpa using hf') he,
    (Push.side g (hg.differentiableAt (by simp)) x).deriv]
  simp [hz, hv, iteratedFDeriv_two_apply]

end YM.Work.F03
