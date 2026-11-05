import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sector
import YM.Push.ABSOLUTE_SUMS.Mixed

/-!
# Cut log for optional terms and frozen shell

Output V-dependent logs needed on *potential* stencils even if sector
not realizable; extend across far group globally with cutoff at a
slightly larger threshold. In particular post-L constants don't use a
condition `Plot(actual)` outside the compulsory halo. Smooth germ in
actual group projections, not differentiating using `plog` at arbitrary
uncontrolled values.
-/

set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Precision Push.SectorMeasure  Channel Next.Fluctuations
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}

/-- Chord threshold rather than algebra norm; identity radius requested
at the end (earlier than chart/kernel computations). -/
def cutLog (χ : Chi) (d : ℝ) (U : G.El) : G.Color := χ.innerShare d (G.chord U) • G.plog (G.mat U)

/-- Include Borel at these scales AND actual right inverse at small arguments. -/
structure Reliable (G : Gauge) (d γ : ℝ) : Prop where
  down : 0 < d
  price : 0 < γ
  right (u : G.El) : G.chord u ≤ 2*d → G.lieExp (G.plog (G.mat u))=u
  cap (u : G.El) : G.chord u ≤ 2*d → ‖G.plog (G.mat u)‖ ≤ γ * G.chord u
  patch (u : G.El) : G.chord u ≤ 2*d → ContDiffAt ℝ ω G.plog (G.mat u)
  commute (u v : G.El) : G.chord u ≤ 2*d → G.plog (G.mat (v*u*v⁻¹)) = G.adjoint v (G.plog (G.mat u))
  inv (u : G.El) : G.chord u ≤ 2*d → G.plog (G.mat u⁻¹) = -G.plog (G.mat u)

lemma reliable (G : Gauge) : ∃ γ r : ℝ, 0<r ∧ ∀ d : ℝ,0<d → d≤r → Reliable G d γ := by
  obtain ⟨C,s,hC,hs,h⟩ := log_chart_cost G
  obtain ⟨t,ht,H⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp (G.plog_diff.eventually (by simp))
  obtain ⟨R,hR,HR⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp G.plog_left
  have hc := G.colorScale_pos
  let X := min s <| min (t/G.colorScale) (R/C)
  have hX : 0<X := lt_min hs (lt_min (div_pos ht hc) (div_pos hR hC))
  refine ⟨C,X/2,half_pos hX,fun d hd he => ?_⟩
  have hp (u : G.El) (hg : G.chord u ≤ 2*d) : G.chord u ≤ X := by linarith
  have hx (u : G.El) (hf : G.chord u ≤ 2*d) := h _ ((hp u hf).trans (min_le_left ..))
  have hy (u : G.El) (hf : G.chord u ≤ 2*d) : ‖G.plog (G.mat u)‖ ≤ R := by
    refine (hx u hf).2.trans ?_
    rw [mul_comm]; exact (le_div_iff₀ hC).mp ((hp u hf).trans ((min_le_right ..).trans (min_le_right ..)))
  have hw (x : G.Color) (hr : ‖x‖ ≤ R) : G.plog (G.mat (G.lieExp x))=x := HR (by simpa using hr)
  refine ⟨hd,hC,fun u hf => (hx u hf).1,fun u hf => (hx u hf).2,?_,?_,?_⟩
  · intro u hf
    have hg := (le_div_iff₀ hc).mp ((hp u hf).trans ((min_le_right ..).trans (min_le_left ..)))
    exact H (Metric.mem_closedBall.mpr (by rw [dist_eq_norm, ← chord_dist, mul_comm]; exact hg))
  · intro u v hf
    have hu := hw (G.adjoint v (G.plog (G.mat u))) (by rw [G.norm_adjoint]; exact hy u hf)
    rwa [exp_adjoint,(hx u hf).1] at hu
  intro u hf
  have hu := hw (-G.plog (G.mat u)) (by rw [norm_neg]; exact hy u hf)
  rwa [Work.F03.exp_neg_color,(hx u hf).1] at hu

lemma Reliable.kept {d γ : ℝ} (h : Reliable G d γ) (χ : Chi) (u : G.El) (hu : G.chord u ≤ d) :
    cutLog χ d u = G.plog (G.mat u) := by
  have he : G.chord u / d ≤ 1 := (div_le_one h.down).2 hu
  have hp : 0 ≤ G.chord u / d := div_nonneg (G.chord_nonneg _) h.down.le
  have hh := χ.to_one ((G.chord u/d)^2) (by nlinarith)
  rw [cutLog, Chi.innerShare, hh,one_smul]

lemma Reliable.use {d γ : ℝ} (h : Reliable G d γ) (χ : Chi) (u : G.El) :
    ‖cutLog χ d u‖ ≤ γ*(2*d) := by
  by_cases he : χ.innerShare d (G.chord u) = 0
  · simp only [cutLog, he,zero_smul,norm_zero]
    exact mul_nonneg h.price.le (by linarith [h.down])
  have hx := χ.chosen_lt _ _ h.down he
  rw [cutLog,norm_smul,Real.norm_of_nonneg (show 0 ≤ χ.innerShare d _ from (χ.range ((G.chord u/d)^2)).1)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.range _).2).trans
    ((h.cap u hx.le).trans (mul_le_mul_of_nonneg_left hx.le h.price.le))

lemma Reliable.conjugate {d γ : ℝ} (h : Reliable G d γ) (χ : Chi) (u v : G.El) :
    cutLog χ d (v*u*v⁻¹) = G.adjoint v (cutLog χ d u) := by
  unfold cutLog; rw [G.chord_conj]; by_cases he : χ.innerShare d (G.chord u) = 0
  · rw [he,zero_smul,zero_smul,map_zero]
  rw [map_smul, h.commute u _ (χ.chosen_lt _ _ h.down he).le]

lemma Reliable.inverse {d γ : ℝ} (h : Reliable G d γ) (χ : Chi) (u : G.El) :
    cutLog χ d u⁻¹ = -cutLog χ d u := by
  unfold cutLog; rw [G.chord_inv]; by_cases he : χ.innerShare d (G.chord u) = 0
  · rw [he,zero_smul,zero_smul,neg_zero]
  rw [h.inv u (χ.chosen_lt _ _ h.down he).le,smul_neg]

attribute [local instance] Gauge.frobInner

lemma Reliable.smooth {d γ : ℝ} (h : Reliable G d γ) (χ : Chi) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : E → G.El} {x : E}
    (hp : ContDiffAt ℝ ∞ (fun y => G.mat (U y)) x) : ContDiffAt ℝ ∞ (fun y => cutLog χ d (U y)) x := by
  have hv : ContDiffAt ℝ ∞ (fun y => χ.innerShare d (G.chord (U y))) x := by
    unfold Chi.innerShare
    simp_rw [Gauge.chord,div_pow]
    have he := (contDiff_norm_sq ℝ).contDiffAt.comp (f:=fun y => G.mat (U y)-1) x (hp.sub contDiffAt_const)
    exact χ.smooth.contDiffAt.comp x ((he.div_const _).div_const _)
  by_cases hk : G.chord (U x) ≤ 2*d
  · exact hv.smul ((h.patch _ hk).of_le (show (∞:WithTop _) ≤ ω from le_top) |>.comp x (f:=fun x => G.mat (U x)) hp)
  have ht : ContinuousAt U x := (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr hp.continuousAt
  have he : ∀ᶠ y in 𝓝 x, 2*d < G.chord (U y) := (G.continuous_chord.continuousAt.comp ht).eventually
    (lt_mem_nhds (lt_of_not_ge hk))
  refine (contDiffAt_const (c:=(0:G.Color))).congr_of_eventuallyEq ?_
  filter_upwards [he] with y hy
  have hu : χ.innerShare d (G.chord (U y)) = 0 := by
    by_contra hg; exact (χ.chosen_lt _ _ h.down hg).not_ge hy.le
  rw [cutLog,hu,zero_smul]

lemma Reliable.borel {d γ : ℝ} (h : Reliable G d γ) (χ : Chi) : Measurable (cutLog χ d (G:=G)) := by
  suffices he : Continuous (cutLog χ d (G:=G)) from he.measurable
  rw [continuous_iff_continuousAt]; intro u
  by_cases hx : G.chord u ≤ 2*d
  · have hp : ContinuousAt (fun v : G.El => χ.innerShare d (G.chord v)) u := by
      unfold Chi.innerShare; exact (χ.smooth.continuous.comp (f:=fun v : G.El => (G.chord v/d)^2) (by fun_prop)).continuousAt
    exact hp.smul ((h.patch _ hx).continuousAt.comp (f:=G.mat) G.continuous_mat.continuousAt)
  refine ContinuousAt.congr (f := fun _ : G.El => (0:G.Color)) continuousAt_const ?_
  have he : ∀ᶠ v in 𝓝 u, 2*d < G.chord v := G.continuous_chord.continuousAt.eventually
    (lt_mem_nhds (lt_of_not_ge hx))
  filter_upwards [he] with v hv
  have hk : χ.innerShare d (G.chord v)=0 := by
    by_contra hu; exact (χ.chosen_lt _ _ h.down hu).not_ge hv.le
  rw [cutLog,hk,zero_smul]
end YM.ConnectedActivityE6
