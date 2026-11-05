import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import YM.Analysis.Polydisc
import YM.Bid.Tar
import YM.Org.Twist



/-!
# C11: thicken the spectral cone and smooth by convolution

Work directly on `Points n`, with its Euclidean distance (also when `n = 0`). Use the
open 2-thickening of `coneM n` for the unsmoothed indicator and a compactly supported
unit-integral bump with outer radius `1/2` for smoothing. We keep slack in the outer
thickening to cover the *closure* of the resulting support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C11
open YM.Boundary
open Function Set Filter Metric MeasureTheory
open scoped ContDiff Convolution Pointwise

private theorem negInvariant (n : ℕ) : (volume : Measure (Points n)).IsNegInvariant :=
  ⟨(LinearIsometryEquiv.neg ℝ : Points n ≃ₗᵢ[ℝ] Points n).measurePreserving.map_eq⟩

/-- Global bounds on all derivatives (in `Points` coordinates) when convolving a smooth
compactly supported function against a locally integrable scalar bounded by one in norm.
Keeping the left and output spaces general lets us repeatedly put the derivatives on the
left factor. -/
private theorem convolution_bound {n : ℕ} {f : Points n → ℝ}
    (hf : LocallyIntegrable f volume) (hb : ∀ x, ‖f x‖ ≤ 1) (k : ℕ) :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (L : E →L[ℝ] ℝ →L[ℝ] F) (g : Points n → E),
      HasCompactSupport g → ContDiff ℝ ∞ g →
      ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (g ⋆[L] f) x‖ ≤ C := by
  letI := negInvariant n
  induction k with
  | zero =>
    intro E F _ _ _ _ _ L g hc hg
    refine ⟨∫ t, ‖L‖ * ‖g t‖, fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero, convolution_def]
    refine norm_integral_le_of_norm_le
      ((hg.continuous.integrable_of_hasCompactSupport hc).norm.const_mul _) ?_
    filter_upwards with t
    exact (L.le_opNorm₂ (g t) (f (x - t))).trans (mul_le_of_le_one_right (by positivity) (hb _))
  | succ k ih =>
    intro E F _ _ _ _ _ L g hc hg
    let L' := L.precompL (Points n)
    have hderiv : fderiv ℝ (g ⋆[L] f) = fderiv ℝ g ⋆[L'] f :=
      funext fun x => (hc.hasFDerivAt_convolution_left L (hg.of_le (by simp)) hf x).fderiv
    obtain ⟨C, hC⟩ := ih L' (fderiv ℝ g) (hc.fderiv ℝ) ((contDiff_infty_iff_fderiv.mp hg).2)
    refine ⟨C, fun x => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, hderiv]
    exact hC x

theorem answer : YM.Bid.C11 := by
  classical
  intro n
  let B := Probe.bud (0 : Points n) (1 / 4) (by norm_num)
  let U := thickening 2 (coneM n)
  let g := B.normed volume
  let f := U.indicator (fun _ => (1 : ℝ))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hr : B.rOut = 1 / 2 := by norm_num [B, Probe.bud]
  refine ⟨{ cut := g ⋆[L] f, uses := ?_, immediate := ?_, supported := ?_ }⟩
  · have hU : MeasurableSet U := isOpen_thickening.measurableSet
    have hf : LocallyIntegrable f volume := (locallyIntegrable_const (1 : ℝ)).indicator hU
    have hc : HasCompactSupport g := B.hasCompactSupport_normed
    have hg : ContDiff ℝ ∞ g := B.contDiff_normed
    have hb (x) : ‖f x‖ ≤ 1 := by by_cases h : x ∈ U <;> simp [f, h]
    letI := negInvariant n
    refine ⟨hc.contDiff_convolution_left L hg hf, fun k => ?_⟩
    obtain ⟨C, hC⟩ := convolution_bound hf hb k L g hc hg
    exact ⟨0, C, fun x => by simpa only [pow_zero, mul_one] using hC x⟩
  · rintro x ⟨z, hz, hd⟩
    have hball (y) (hy : y ∈ ball x B.rOut) : f y = 1 := by
      apply Set.indicator_of_mem
      rw [hr, mem_ball] at hy
      apply mem_thickening_iff.mpr
      exact ⟨z, hz, by linarith [dist_triangle y x z]⟩
    have hx := hball x (mem_ball_self B.rOut_pos)
    calc
      _ = f x := ContDiffBump.normed_convolution_eq_right (φ := B)
        (fun y hy => (hball y hy).trans hx.symm)
      _ = 1 := hx
  · have hs : support (g ⋆[L] f) ⊆ thickening (5 / 2) (coneM n) := by
      refine (support_convolution_subset L).trans ?_
      rintro x hx
      rcases Set.mem_add.mp hx with ⟨t, ht, y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := mem_thickening_iff.mp
        (show y ∈ thickening 2 (coneM n) from Set.support_indicator_subset hy)
      rw [show support g = ball 0 B.rOut from B.support_normed_eq, hr, mem_ball] at ht
      refine mem_thickening_iff.mpr ⟨z, hz, ?_⟩
      have he : dist (t + y) y = dist t 0 := by simp
      linarith [dist_triangle (t + y) y z]
    intro x hx
    apply (mem_thickening_iff (E := coneM n)).mp
    exact cthickening_subset_thickening' (by norm_num) (show (5 / 2 : ℝ) < 3 by norm_num) _
      (closure_thickening_subset_cthickening _ _ (closure_mono hs hx))

end YM.Work.C11
