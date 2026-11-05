import YM.Extension.UV.Holo
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Complexification in uniform sup norms on (potentially many) aligned addresses. Pointwise
holomorphy alone wouldn't give derivative bounds/Fréchet differentiability when all coordinates
are tested. Use interior Cauchy estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.UniformHol
open BoundedContinuousFunction Set Filter Function Topology Metric Asymptotics
open scoped Classical
set_option quotPrecheck false
variable {ι:Type*}
structure Disc (ι:Type*) where
  get : ι
instance : TopologicalSpace (Disc ι):=⊥
instance : DiscreteTopology (Disc ι):=⟨rfl⟩
abbrev UniformOn (ι:Type*) (F:Type*) [PseudoMetricSpace F]:= BoundedContinuousFunction (Disc ι) F
abbrev Rows (ι : Type*) := UniformOn ι ℂ

def pack {F:Type*} [SeminormedAddCommGroup F] (f:ι→F) : UniformOn ι F:=
 if h:∃ C, ∀ i, ‖f i‖ ≤ C then ofNormedAddCommGroupDiscrete (fun i:Disc ι=> f i.get) h.choose (fun i=> h.choose_spec i.get) else 0
lemma equals {F:Type*} [SeminormedAddCommGroup F] {f:ι→F} (h:∃ C, ∀ i, ‖f i‖ ≤ C) (i:ι) : pack f ⟨i⟩=f i:=by unfold pack; rw [dif_pos h]; rfl

def jets (f:ℂ→Rows ι) (x:ℂ) := pack (fun i:ι=> deriv (fun z=> f z ⟨i⟩) x)
private lemma derivative_bound {f:ℂ→ℂ} {x:ℂ} {r M:ℝ} (hr:0<r) (hf:DifferentiableOn ℂ f (ball x r)) (hb:∀ y∈ball x r, ‖f y‖≤M) : ‖deriv f x‖ ≤ M/r := by
   rw [deriv]; exact ((ContinuousLinearMap.le_opNorm ..).trans ((mul_le_mul_of_nonneg_right (cauchy_bound hf hr hb) (by positivity)).trans_eq (by simp)))

set_option maxHeartbeats 450000 in
lemma hasDeriv (f:ℂ→Rows ι) (x:ℂ) (r M:ℝ) (hr:0<r) (hM:0≤M)
   (hf : ∀ i, DifferentiableOn ℂ (fun y=> f y i) (ball x (4*r))) (hb:∀ y∈ball x (4*r),∀ i, ‖f y i‖≤M) :
    HasDerivAt f (jets f x) x := by
  classical
  have h (k:ℝ) {y:ℂ} (hy:y∈ball x ((k-1)*r)) : ball y r ⊆ ball x (k*r) := fun q hq=> by
    apply mem_ball.mpr; linarith [(mem_ball.mp hy),(mem_ball.mp hq),dist_triangle q y x]
  have HD i : DifferentiableOn ℂ (deriv (fun z=> f z i)) (ball x (3*r)) := ((hf i).deriv isOpen_ball).mono (ball_subset_ball (by linarith))
  have hv {y:ℂ} (hy:y∈ball x (3*r)) i : ‖deriv (fun z=>f z i) y‖ ≤ M/r:= by
    have hq: ball y r ⊆ ball x (4*r):= h 4 (by convert hy using 2; norm_num)
    exact derivative_bound hr ((hf i).mono hq) (fun v hw=> hb _ (hq hw) i)
  have hj i : jets f x i = deriv (fun z=> f z i) x:= by
    cases i with
    | mk i => exact equals ⟨M/r,fun i:ι=> hv (mem_ball_self (by positivity)) ⟨i⟩⟩ _
  let C:= (M/r)/r
  have hD i y (hy:y∈ball x (2*r)): ‖deriv (deriv (fun z=>f z i)) y‖ ≤ C:= by
    have hq : ball y r ⊆ ball x (3*r):= h 3 (by convert hy using 2; norm_num)
    exact derivative_bound hr ((HD i).mono hq) fun z hz=> hv (hq hz) i
  have hle {z:ℂ} (hz:z∈ ball x r) : ‖f z-f x-(z-x)•jets f x‖ ≤ C*‖z-x‖*‖z-x‖ :=by
    let s:=closedBall x ‖z-x‖
    have hs {v:ℂ} (hv:v∈s) : v∈ball x (2*r):= mem_ball.mpr (by have hv:= mem_closedBall.mp hv; rw [← dist_eq_norm] at hv; linarith [mem_ball.mp hz])
    have hs₁ {v:ℂ} (hv:v∈s): v∈ball x (3*r):= ball_subset_ball (by linarith) (hs hv)
    have hs₂ {v:ℂ} (hv:v∈s): v∈ball x (4*r):= ball_subset_ball (by linarith) (hs hv)
    apply (BoundedContinuousFunction.norm_le (by unfold C; positivity)).2 fun i=>?_
    change ‖(f z i)-(f x i)-(z-x)*(jets f x i)‖ ≤ _
    let H (z:ℂ):=f z i
    rw [hj]
    change ‖H z-H x-(z-x)*deriv H x‖ ≤ _
    let g (y:ℂ):=H y-y*deriv H x
    have hw : ‖H z-H x-(z-x)*deriv H x‖=‖g z-g x‖:= congr_arg _ (by unfold g; ring)
    rw [hw]
    have hx' : x∈s:= mem_closedBall.mpr (dist_self x ▸ norm_nonneg _)
    have hz' : z∈s:= by rw [mem_closedBall,dist_eq_norm]
    refine (convex_closedBall ..).norm_image_sub_le_of_norm_deriv_le (𝕜:=ℂ) (s:=s) ?_ ?_ hx' hz'
    · intro z hz; exact (((hf i).differentiableAt (isOpen_ball.mem_nhds (hs₂ hz))).hasDerivAt.sub ((hasDerivAt_id z).mul_const _)).differentiableAt
    intro z₀ h₀
    have he := (((hf i).differentiableAt (isOpen_ball.mem_nhds (hs₂ h₀))).hasDerivAt.sub ((hasDerivAt_id' z₀).mul_const (deriv H x))).deriv; rw [show deriv g z₀=_ from he,one_mul]
    exact ((convex_closedBall x ‖z-x‖).norm_image_sub_le_of_norm_deriv_le (𝕜:=ℂ) (fun z hz=> (HD _).differentiableAt (isOpen_ball.mem_nhds (hs₁ hz))) (fun z hz=> hD _ z (hs hz)) hx' h₀).trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact mem_closedBall.mp h₀) (by unfold C; positivity))
  apply HasDerivAt.of_isLittleO; rw [isLittleO_iff]; intro c hc
  have ht : ContinuousAt (fun y : ℂ=> C*‖y-(x:ℂ)‖) x:= by exact ((continuousAt_id.sub continuousAt_const).norm |>.const_mul C).tendsto
  filter_upwards [ht.tendsto.eventually_lt_const (by simpa using hc), Metric.ball_mem_nhds x hr] with y hy h₂
  exact (hle h₂).trans (mul_le_mul_of_nonneg_right hy.le (norm_nonneg _))

lemma liftOn {f:ℂ→ι→ℂ} {U:Set ℂ} (hu:IsOpen U) (hd:∀ i,DifferentiableOn ℂ (fun z=>f z i) U)
    (hl:∀ x∈U,∃ V∈ 𝓝 x,∃ M : ℝ,∀ z∈V,∀ i,‖f z i‖ ≤ M): DifferentiableOn ℂ (fun z=>pack (f z)) U:= by
   intro x hx
   obtain ⟨V,hV,M,hM⟩:= hl x hx
   obtain ⟨r,hr,h⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (hu.mem_nhds hx))
   have ht {z:ℂ} (hz:z∈ball x (4*(r/4))) i : pack (f z) i=f z i.get:= by
      cases i; exact equals ⟨M,hM _ ((h (show z∈_ by convert hz using 2; ring)).1)⟩ _
   refine (hasDeriv (fun z=>pack (f z)) x (r/4) (max 0 M) (by positivity) (le_max_left ..) ?_ ?_).differentiableAt.differentiableWithinAt
   · exact fun i=> ((hd i.get).mono (fun z hz => (h (show z∈_ by convert hz using 2; ring)).2)).congr fun z hz=> (ht hz i)
   exact fun z hz i => (ht hz i).symm ▸ (hM _ (h (show z∈_ by convert hz using 2; ring)).1 _).trans (le_max_right ..)
end YM.Extension.UV.UniformHol
