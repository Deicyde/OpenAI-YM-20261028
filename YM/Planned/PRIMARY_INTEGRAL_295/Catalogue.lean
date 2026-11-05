import YM.Planned.PRIMARY_INTEGRAL_295.Streets
import YM.Progress.STATIONARY_SCENES.Response


/-!
# True μ_tangent core and norms at all forests

With `A0` strip price C/L, φ etc cost C_j at pre length in the
orthonormal color norm. Source contact uses actual ratio; estimates in
full torus sup, arbitrary size. No θ-transports promoted as uniform post
without meeting Bind & budget proofs.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Streets
open Function Filter Set Metric Lattice RG Wilson Labels Source
open Precision Exterior Bloch Work.F08 Tree Next.Free Carrier Place  Progress.StationaryScenes
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {c f : Side} {S : StepData c f} {G : Gauge} {T : Finset Cover}



lemma stream_cost (S : StepData c f) (F : Forest S.ratio) : ‖streamFill S F (G:=G)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one; intro v hv
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro x; unfold streamFill; rw [ContinuousLinearMap.pi_apply]; split
  · simp
  exact (norm_le_pi_norm v ⟨x,by assumption⟩).trans hv.le

def fee (G : Gauge) := (1+(Fintype.card G.ColorIndex):ℝ)
lemma fee_pos (G:Gauge) : 1 ≤ fee G := by unfold fee; simp

lemma uniformize (x : G.Color) (C:ℝ) (h:0≤C) (hv:∀ j, |x j|≤C) : ‖x‖ ≤ fee G*C := by
  let A:=(Fintype.card G.ColorIndex:ℝ); let f:=fee G
  have he : ‖x‖^2 ≤ A * C^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; refine (Finset.sum_le_sum (g:=fun _ => C^2) fun i _=>?_).trans_eq (by simp [A]);
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hv _) _
  have hp : 1 ≤ f:=fee_pos _; have ht : A ≤ f^2 := by unfold f fee A; nlinarith
  have hz : ‖x‖^2 ≤ (f*C)^2 := he.trans ((mul_le_mul_of_nonneg_right ht (by positivity)).trans_eq (mul_pow ..).symm)
  change ‖x‖≤f*C; nlinarith only [mul_nonneg (zero_le_one.trans hp) h, norm_nonneg x,hz]

section Prices
variable (S : StepData c f) (F : Forest S.ratio) (W : Lines S.ratio.count) (G)
variable {σ C : ℝ} (hσ : 0≤σ) (hT : W.strip σ (C / (S.ratio.count.val:ℝ)))

include hσ in
private lemma tendon (x:Site f) (v:Dir G c) (h:‖v‖≤1) (j:G.ColorIndex) (y:Body 1 c) : |v y j| ≤ crossW S.ratio σ x y.1 := by
  have he : 1 ≤ crossW S.ratio σ x y.1 := by unfold crossW; apply Real.one_le_exp; positivity
  exact (PiLp.norm_apply_le (v y) j).trans ((norm_le_pi_norm ..).trans (h.trans he))

include hσ hT
lemma surf_cost : ‖axisPhi S F W (G:=G)‖ ≤ fee G * Response.correction S.patch.J σ C := by
  have hc := Response.nonneg S.patch.J σ C
  have hv:=fee_pos G
  have hb:0≤Response.correction S.patch.J σ C:= by unfold Response.correction; positivity
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity); intro v hv'
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro x
  apply uniformize _ _ hb; intro j
  have he := Response.straighten_price S hσ hT F x x (by simp) (parts G 1 v j) (tendon G S hσ _ v hv'.le j)
  change |pledge (straighten _ _ _) v _ j|≤_; rw [code]; exact he

lemma aim_cost : ‖crick S F W (G:=G)‖ ≤ fee G*(Response.total S.patch.J σ C + Real.exp σ) := by
  have he:=Response.nonneg S.patch.J σ C; have hp:=fee_pos G
  have hc : 0 ≤ Response.total S.patch.J σ C + Real.exp σ := by unfold Response.total Response.correction; positivity
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity); intro v hv
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro x
  apply uniformize _ _ hc; intro j; rw [crick_relative]; exact Response.tangent_apply S hσ hT F x j v (tendon G S hσ _ v hv.le j)
end Prices
end YM.Planned.PrimaryIntegral295.Streets
