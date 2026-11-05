import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic



/-! Banquet from mathlib Cauchy. Actual variables have positively tilted radii. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Plotter
open Filter Function MeasureTheory Metric Complex Finset
open scoped Topology
variable {ι : Type*} [MeasurableSpace ι]

def room (r : ℝ) (f : ℂ→ℂ) (C : ℝ) := DifferentiableOn ℂ f (Metric.ball 0 r) ∧
    ∀ z∈Metric.ball 0 r, ‖f z‖≤C

lemma chapel (μ : Measure ι) (F : ℂ → ι → ℂ) {b : ι → ℝ} (h : Integrable b μ) (r : ℝ) (hh : ∀ z, Measurable (F z))
    (hp : ∀ i,Differentiable ℂ (fun z => F z i)) (ht : ∀ z : ℂ,z ∈ Metric.ball 0 r → ∀ i, ‖F z i‖ ≤ b i) :
    (∀ z∈ Metric.ball 0 r,Integrable (F z) μ) ∧ room r (fun z => ∫ i,F z i∂μ) (∫ i,b i ∂μ) := by
  let f z := ∫ i,F z i ∂μ
  have hm z (he : z∈ball (0:ℂ) r) : Integrable (F z) μ := h.mono' (hh z).aestronglyMeasurable (Eventually.of_forall (ht z he))
  refine ⟨hm,fun z hz => DifferentiableAt.differentiableWithinAt ?_,fun z hz => (norm_integral_le_integral_norm _).trans
    (integral_mono (hm z hz).norm h (ht z hz))⟩
  rw [mem_ball,dist_zero_right] at hz
  let v := (r - ‖z‖)/3; have hv : 0<v := div_pos (sub_pos.mpr hz) (by norm_num)
  let D p i := deriv (fun x => F x i) p
  have he (p : ℂ) (i : ι) : HasDerivAt (fun x => F x i) (D p i) p := (hp i p).hasDerivAt
  have hy p (hy : p ∈ ball z v) (i) : ‖D p i‖ ≤ b i / v := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hv (hp i).diffContOnCl
    intro q hq; apply ht
    rw [mem_ball]; rw [mem_ball] at hy; apply lt_of_le_of_lt (dist_triangle q p 0)
    rw [mem_sphere] at hq; have hx := dist_triangle p z 0; rw [dist_zero_right z] at hx; dsimp [v] at *; linarith
  have hf : Measurable (D z) := by
    apply measurable_of_tendsto_metrizable' (𝓝[≠] z) _ <| tendsto_pi_nhds.mpr (fun i => show Tendsto
      (fun y => (y-z)⁻¹ • (F y i-F z i)) _ _ from hasDerivAt_iff_tendsto_slope.mp (he z i))
    intro i; exact ((hh i).sub (hh z)).const_smul (i-z)⁻¹
  have hq := hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z hv) (Eventually.of_forall fun z =>
    (hh z).aestronglyMeasurable (μ:=μ)) (hm z (mem_ball.mpr <| by rw [dist_zero_right]; exact hz)) hf.aestronglyMeasurable
    (show ∀ᵐ i ∂μ, ∀ w∈ball z v, ‖D w i‖≤b i /v from Eventually.of_forall fun i w hw => hy w hw i)
    (h.div_const _) (Eventually.of_forall fun i w _ => he w i)
  exact hq.2.differentiableAt

-- helper for real pulses, eventual enough



end YM.AnalyticNext.ConnectedActivity.Plotter
