import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Scalar-tested holder to vector holomorphy

No assumption all dual data -- just separating set and vector continuity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Analysis
open Function Set Filter Metric Complex
open scoped Topology BigOperators NNReal ENNReal Real InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma commute_integral (L : E →L[ℂ] ℂ) {f : ℂ → E} (c : ℂ) (r : ℝ) (hf : CircleIntegrable f c r) :
    L (∮ z in C(c,r), f z) = (∮ z in C(c,r), L (f z)) := by
  unfold circleIntegral
  simpa only [map_smul] using! (L.intervalIntegral_comp_comm hf.out).symm

lemma lift_weak (S : Set (E →L[ℂ] ℂ)) (hs : ∀ (x y : E), (∀ L ∈ S, L x=L y) → x=y) {f : ℂ → E}
    {U : Set ℂ} (hu : IsOpen U) (hc : ContinuousOn f U) (h : ∀ L ∈ S, DifferentiableOn ℂ (fun z => L (f z)) U) :
    AnalyticOnNhd ℂ f U := by
  intro z hz
  obtain ⟨r,hr,hR⟩ := nhds_basis_closedBall.mem_iff.mp (hu.mem_nhds hz)
  lift r to ℝ≥0 using hr.le
  have he : HasFPowerSeriesOnBall f (cauchyPowerSeries f z r) z r := by
    refine { r_le := le_radius_cauchyPowerSeries _ _ _
             r_pos := ENNReal.coe_pos.2 hr
             hasSum := ?_ }
    intro w hw
    have hw' : z+w ∈ ball z (r:ℝ) := by
      simpa only [add_mem_ball_iff_norm, ← coe_nnnorm, mem_eball_zero_iff, NNReal.coe_lt_coe, enorm_lt_coe] using hw
    have hh : CircleIntegrable (fun u => (u-(z+w))⁻¹ • f u) z (r:ℝ) := by
      refine (ContinuousOn.circleIntegrable r.2 ?_)
      refine ContinuousOn.smul  ((continuousOn_id.sub continuousOn_const).inv₀ fun x hx => ?_)
        (hc.mono (sphere_subset_closedBall.trans hR))
      intro he
      change x-(z+w)=0 at he
      have hv := sub_eq_zero.mp he; rw [hv] at hx
      exact (mem_ball.mp hw').ne (mem_sphere.mp hx)
    have hx : (2*Real.pi*Complex.I : ℂ) • f (z+w) = ∮ u in C(z,r), (u-(z+w))⁻¹ • f u := by
      apply hs; intro L hL
      rw [map_smul,commute_integral L z r hh]
      simp_rw [map_smul]; exact ((h L hL).mono hR |>.circleIntegral_sub_inv_smul hw').symm
    have hb : f (z+w)=(2*Real.pi*Complex.I : ℂ)⁻¹ • ∮ u in C(z,r), (u-(z+w))⁻¹ • f u := by
      rw [← hx,inv_smul_smul₀ (by exact Complex.two_pi_I_ne_zero)]
    rw [hb]
    exact (hasFPowerSeriesOn_cauchy_integral ((hc.mono (sphere_subset_closedBall.trans hR)).circleIntegrable r.2) hr).hasSum hw
  exact he.analyticAt
end YM.Analysis
