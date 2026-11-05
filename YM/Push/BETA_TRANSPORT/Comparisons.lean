import YM.Push.BETA_TRANSPORT.Gibbs

/-! Denominator and density comparisons with no upper bound required on β. Costs explicitly
extensive, or per-site in a log. Pointwise inequality on unmarked masses; averaged norm
on signed or vector-valued insertions. Includes crossing β=0. No exchange of a cutoff
limit with a derivative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Gibbs MeasureTheory Wilson Lattice Pressure RG Filter Set
open scoped Topology Matrix.Norms.Frobenius BigOperators

structure LogBound (f : ℝ → ℝ) (C : ℝ) : Prop where
  positive (x : ℝ) : 0 < f x
  diff : Differentiable ℝ f
  slope (x : ℝ) : |deriv f x| ≤ C * f x

namespace LogBound
variable {f : ℝ → ℝ} {C : ℝ} (h : LogBound f C)
include h
lemma derivative (x : ℝ) : ‖deriv (fun y => Real.log (f y)) x‖ ≤ C := by
  rw [((h.diff x).hasDerivAt.log (h.positive x).ne').deriv, norm_div,Real.norm_of_nonneg (h.positive x).le]
  exact (div_le_iff₀ (h.positive x)).mpr (h.slope x)
lemma oscillation (x y : ℝ) : |Real.log (f y) - Real.log (f x)| ≤ C * |y - x| :=
  (convex_univ (𝕜:=ℝ)).norm_image_sub_le_of_norm_deriv_le (fun z _ => ((h.diff z).hasDerivAt.log
    (h.positive z).ne').differentiableAt) (fun z _ => h.derivative z) (mem_univ x) (mem_univ y)
lemma compare (x y : ℝ) : f y ≤ cost C |y-x| * f x := by
  rw [cost,← Real.exp_log (h.positive x),← Real.exp_add,← Real.exp_log (h.positive y)]
  apply Real.exp_monotone
  rw [mul_comm |y-x|]; exact sub_le_iff_le_add.mp (le_of_abs_le (h.oscillation ..))
lemma bounds (x y : ℝ) : (cost C |y-x|)⁻¹ * f x ≤ f y ∧ f y ≤ cost C |y-x| * f x := by
  rw [inv_mul_le_iff₀ (cost_pos C _)]
  exact ⟨by simpa only [abs_sub_comm y] using h.compare y x,h.compare x y⟩
end LogBound

variable {G : Gauge} {c f n : Side} (S : StepData c f)











/-- Pointwise price linear to first order, local radius depending only on |x-y|.
Uniform across β, relative to the weight at x. -/
lemma LogBound.change {f : ℝ → ℝ} {C : ℝ} (h : LogBound f C) (x y : ℝ) :
    |f y - f x| ≤ (cost C |y-x| - 1) * f x := by
  obtain ⟨h1,h2⟩ := h.bounds x y
  let K := cost C |y-x|
  have hK : 0 < K := cost_pos ..
  have he : 2-K ≤ K⁻¹ := by rw [inv_eq_one_div,le_div_iff₀ hK]; nlinarith [sq_nonneg (K-1)]
  refine abs_le.mpr ⟨?_, by linarith⟩
  change -((K-1)*f x) ≤ _; have := (mul_le_mul_of_nonneg_right he (h.positive x).le).trans h1
  linarith
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [CompleteSpace X]
set_option linter.unusedSectionVars false



end YM.Push.BetaTransport
