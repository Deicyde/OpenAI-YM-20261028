import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Uniqueness
/-!
Normal families argument on one-complex-parameter slices. Works for general
convergence filters (e.g. boundary limits as well as character dependence).
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Set Filter Metric
open scoped Topology

variable {α : Type*} {L : Filter α} {F : α → ℂ → ℂ} {U : Set ℂ} {x y : ℂ}

/-- Local bound need only be on a tail, no control of early functions. -/
def boundedHere (F : α → ℂ → ℂ) (L : Filter α) (x : ℂ) : Prop :=
  ∃ (r : ℝ), 0<r ∧ ∃ C : ℝ, ∀ᶠ a in L, ∀ z ∈ ball x r, ‖F a z‖ ≤ C

theorem nearby (h : IsOpen U) (he : ∀ᶠ a in L, DifferentiableOn ℂ (F a) U) (hx : x∈U)
    (hh : boundedHere F L x) : ∃ D : ℝ, 0<D ∧ ∃ T ∈ 𝓝 x, T ⊆ U ∧
    ∀ᶠ a in L, ∀ y ∈ T, dist (F a y) (F a x) ≤ D * dist y x := by
  obtain ⟨r,hr,A,hA⟩ := hh
  obtain ⟨s,hs,hU⟩ := Metric.mem_nhds_iff.mp (h.mem_nhds hx)
  let t := (min r s)/2
  have ht : 0<t := by unfold t; exact div_pos (lt_min hr hs) (by norm_num)
  let C := max 1 (A/t)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hp : ball x (t+t) ⊆ ball x r ∩ U := by
    have he : t+t=min r s := by unfold t; ring
    rw [he]; exact subset_inter (ball_subset_ball (min_le_left ..)) ((ball_subset_ball (min_le_right ..)).trans hU)
  have hk : ball x t ⊆ U := (ball_subset_ball (x:=x) (show t≤t+t by linarith)).trans (hp.trans inter_subset_right)
  refine ⟨C,hC,ball x t,ball_mem_nhds x ht,hk,?_⟩
  filter_upwards [he,hA] with a ha hb y hy
  have hw (z : ℂ) (hz : z∈ball x t) : ‖fderiv ℂ (F a) z‖ ≤ C := by
    have hm : closedBall z t ⊆ ball x r ∩ U := by
      intro w hw
      exact hp (mem_ball.mpr (lt_of_le_of_lt (dist_triangle w z x) (add_lt_add_of_le_of_lt hw hz)))
    rw [← norm_deriv_eq_norm_fderiv, ← Complex.cderiv_eq_deriv h ha ht (hm.trans inter_subset_right)]
    exact (Complex.norm_cderiv_le ht fun w hw => hb w (hm (sphere_subset_closedBall hw)).1).trans (le_max_right ..)
  simp only [dist_eq_norm]
  exact (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => ha.differentiableAt (h.mem_nhds (hk hz))) hw (mem_ball_self ht) hy

lemma equi_on [L.NeBot] {g : ℂ → ℂ} (h : IsOpen U)
    (he : ∀ᶠ a in L, DifferentiableOn ℂ (F a) U)
    (hb : ∀ x∈U, boundedHere F L x) (hg : ∀ x∈U, Tendsto (fun a => F a x) L (𝓝 (g x))) :
    TendstoLocallyUniformlyOn F g L U := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hp x hx
  obtain ⟨C,hC,T,hT,ht,hh⟩ := nearby h he hx (hb x hx)
  let r := ε / 4 / C
  have hr : 0<r := by unfold r; positivity
  let S := ball x r ∩ T
  refine ⟨S,nhdsWithin_le_nhds (inter_mem (ball_mem_nhds x hr) hT), ?_⟩
  filter_upwards [hh,Metric.tendsto_nhds.mp (hg x hx) (ε/4) (by positivity)] with a ha hy
  intro y (hq : y∈ball x r∩T)
  have hh' : C*dist y x < ε/4 := by
    rw [mul_comm]; exact (lt_div_iff₀ hC).mp hq.1
  have hv : dist (g y) (g x) ≤ C*dist y x := le_of_tendsto ((hg _ (ht hq.2)).dist (hg x hx))
    (hh.mono fun a ha => ha y hq.2)
  have hw := ha y hq.2
  have h₁ := dist_triangle (g y) (g x) (F a x)
  have h₂ := dist_triangle (g y) (F a x) (F a y)
  rw [dist_comm] at hy hw
  linarith

theorem propagate_limit {f : ℂ → ℂ} (h : IsOpen U) (hp : IsPreconnected U)
    (he : ∀ᶠ a in L, DifferentiableOn ℂ (F a) U) (hu : DifferentiableOn ℂ f U)
    (hb : ∀ x∈U, boundedHere F L x) (hx : x∈U)
    (hf : ∃ᶠ z in 𝓝[≠] x, z∈U ∧ Tendsto (fun a => F a z) L (𝓝 (f z))) (hy : y∈U) :
    Tendsto (fun a => F a y) L (𝓝 (f y)) := by
  apply (Filter.tendsto_iff_ultrafilter ..).mpr
  intro l hl
  have hm (z : ℂ) (hz : z∈U) : boundedHere F l z := by
    obtain ⟨r,hr,C,hC⟩ := hb z hz
    exact ⟨r,hr,C,hC.filter_mono hl⟩
  choose g hg using (show ∀ z : ℂ, ∃ u : ℂ, z∈U → Tendsto (fun a => F a z) l (𝓝 u) from by
    intro z; by_cases H : z∈U
    · obtain ⟨r,hr,C,hC⟩ := hm z H
      have HH : closedBall (0:ℂ) C ∈ l.map (fun a => F a z) := by
        exact hC.mono (fun a ha => mem_closedBall.mpr (by simpa using ha z (mem_ball_self hr)))
      obtain ⟨w, -, hW⟩ := (isCompact_closedBall (0:ℂ) C).ultrafilter_le_nhds' _ HH
      exact ⟨w,fun _ => hW⟩
    exact ⟨0,fun h => (H h).elim⟩)
  have hD := he.filter_mono hl
  have hg' : AnalyticOnNhd ℂ g U := ((equi_on h hD hm hg).differentiableOn hD h).analyticOnNhd h
  have hG := hg'.eqOn_of_preconnected_of_frequently_eq (hu.analyticOnNhd h) hp hx (hf.mono
    (fun z hh => tendsto_nhds_unique (hg z hh.1) (hh.2.mono_left hl)))
  rw [← hG hy]; exact hg y hy
end YM.EveryPhase
