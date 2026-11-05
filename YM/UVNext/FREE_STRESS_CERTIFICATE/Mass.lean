import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Next.UV_STRESS.Across



/-!
# The 4d mass used to regularize the single-contraction contribution to the
stress normalization (optional). Not a distributional extension of Wick products.
Includes the actual normalization `Maxwell.normal` and Euclidean volume.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Set MeasureTheory Filter Analysis
open scoped Topology

def droplet (r : ℝ) (x : E4) := 8 * normal * r^2 * (‖x‖^2 + r^2)⁻¹ ^ 3
private def body (x : ℝ) := 8*normal*(x^2+1)⁻¹^3
private def rod (x : ℝ) := 2*normal*(1-(x^2+1)⁻¹)^2

private lemma tilt_rod (x : ℝ) : HasDerivAt rod (x^3 * body x) x := by
  have h := (((((((hasDerivAt_id' x).pow 2).add_const 1).inv (by nlinarith : x^2+1 ≠ 0)).const_sub 1).pow 2).const_mul (2*normal))
  convert! h using 1
  simp only [body, Pi.pow_apply,Pi.inv_apply]; push_cast; field_simp; ring
private lemma slope_rod : Tendsto rod atTop (𝓝 (2*normal)) := by
  have he : Tendsto (fun x : ℝ => x^2+1) atTop atTop := by
    apply tendsto_atTop_mono' atTop (f₁:=fun x => x) _ tendsto_id
    filter_upwards [eventually_ge_atTop 1] with x hx; nlinarith
  have h := tendsto_inv_atTop_zero.comp he
  convert (((tendsto_const_nhds (x:=(2*normal))).mul ((tendsto_const_nhds (x:=(1:ℝ))).sub h |>.pow 2))) using 1
  · rfl
  norm_num
private lemma body_pos (x : ℝ) (h : x∈Ioi (0:ℝ)) : 0 ≤ x^3*body x := by
  have h' : 0<x := h; have := normal_pos; unfold body; positivity

lemma can_rain : Integrable (droplet 1) := by
  rw [show droplet 1 = fun x => body ‖x‖ from by funext; simp [droplet,body], integrable_fun_norm_addHaar]
  simp
  exact integrableOn_Ioi_deriv_of_nonneg' (fun x _ => tilt_rod x) body_pos slope_rod

lemma raindrop : ∫ x : E4, droplet 1 x = 1 := by
  rw [show droplet 1 = fun x => body ‖x‖ from by funext; simp [droplet,body], integral_fun_norm_addHaar]
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => tilt_rod x) body_pos slope_rod
  have hv : volume.real (Metric.ball (0:E4) 1) = Real.pi^2/2 := by
    rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k:=2) (by simp)]
    simp only [ENNReal.ofReal_one,one_pow,one_mul]; rw [ENNReal.toReal_ofReal (by positivity)]; norm_num [Nat.factorial]
  simp [hv,he,rod]
  unfold normal; have hp := Real.pi_pos; field_simp

theorem rains (f : E4→ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun r : ℝ => ∫ x, droplet r x*f x) (𝓝[>] 0) (𝓝 (f 0)) := by
  have hi (r : ℝ) (hr : 0<r) : (∫ x, droplet r x*f x) = ∫ x, droplet 1 x * f (r • x) := by
    have he := Measure.integral_comp_smul (volume (α:=E4)) (fun y => droplet r y*f y) r
    have hv (x : E4) : droplet r (r • x)*f (r • x) = (r^4)⁻¹ * (droplet 1 x * f (r • x)) := by
      unfold droplet; rw [norm_smul,Real.norm_of_nonneg hr.le]
      have h : 0 < (r * ‖x‖)^2+r^2 := by positivity
      have h' : 0 < ‖x‖^2+(1:ℝ)^2 := by positivity
      field_simp
    simp_rw [hv,smul_eq_mul,show Module.finrank ℝ E4 = 4 by simp,abs_of_nonneg (show 0≤ (r^4:ℝ)⁻¹ by positivity)] at he
    rw [integral_const_mul] at he
    exact (mul_left_cancel₀ (show (r^4)⁻¹ ≠ 0 by positivity) he).symm
  refine Tendsto.congr' (f₁:=fun r : ℝ => ∫ x, droplet 1 x * f (r • x)) ?_ ?_
  · exact (show ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ), r∈Ioi (0 : ℝ) from self_mem_nhdsWithin).mono fun r h => (hi r h).symm
  obtain ⟨c,hc'⟩ := (hc.norm.isCompact_range hf.norm).bddAbove
  have h (x : E4) : ‖f x‖ ≤ c := hc' (mem_range_self x)
  rw [show f 0=(∫ x : E4, droplet 1 x * f 0) by rw [integral_mul_const,raindrop,one_mul]] -- rewriting all f 0 but no issue
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖droplet 1 x‖ * c) ?_ ?_ (can_rain.norm.mul_const c) ?_
  · apply Eventually.of_forall; intro r
    exact can_rain.aestronglyMeasurable.mul (show Continuous (fun x : E4 => f (r • x)) from by fun_prop).aestronglyMeasurable
  · apply Eventually.of_forall; intro r; apply Eventually.of_forall; intro x; rw [norm_mul]; gcongr; exact h _
  · apply Eventually.of_forall; intro x
    rw [show (0:E4)=(0:ℝ) • x from (zero_smul ℝ _).symm]
    exact (continuous_const.mul (hf.comp (continuous_id'.smul continuous_const))).continuousAt.continuousWithinAt

end YM.UVNext.FreeStress
