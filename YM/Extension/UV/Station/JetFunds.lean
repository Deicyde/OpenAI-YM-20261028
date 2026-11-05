import YM.Extension.UV.Station.JetSeq
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.StationaryData
open Function Set Filter RG Wilson
open scoped Topology BigOperators Classical ContDiff
namespace ink
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (p: E→ F) (hp:ContDiff ℂ ω p)
  {x:E} {R C:ℝ} (hR:0<R) (h:∀ y∈Metric.ball x R, ‖p y‖ ≤ C)

def expense (R:ℝ) (k:ℕ) : ℝ:= Nat.rec 1 (fun k c=> c/(R/2^(k+1))) k
lemma expense_zero (R):expense R 0 =1:=rfl
lemma expense_succ (R k):expense R (k+1)=expense R k / (R/2^(k+1)):=rfl
include hR in
lemma expense_pos (k:ℕ):0<expense R k:=by induction k with
  | zero=>exact zero_lt_one
  | succ k hk=> rw [expense_succ]; positivity

include hp h hR in
lemma costed (k:ℕ) y(hy:y∈Metric.ball x (R/2^(k:ℕ))) : ‖iteratedFDeriv ℂ k p y‖ ≤ expense R k*C := by
  induction k generalizing y with
  | zero=> simpa only [expense_zero,norm_iteratedFDeriv_zero,one_mul] using h y (by simpa using hy)
  | succ k hk=>
    have he:= Work.F02.fderiv_bound (hp.differentiable_iteratedFDeriv (m:=k) (by simp)) (by positivity : 0<R/2^k) hk (y:=y) (by rw [show 2^(k+1)=(2:ℝ)^k*2 by rw [pow_succ],show R/((2:ℝ)^k*2)=R/2^k/2 by ring_nf] at hy; exact hy)
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,LinearIsometryEquiv.norm_map,expense_succ]
    exact he.trans_eq (by rw [pow_succ]; ring)

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  {ι:Type*}
  (v : ℕ→ι→ℝ) (z:ι→ℝ) (w:ι→ℝ)
  (q:ι→E→F) (hq:∀ i, ContDiff ℂ ω (q i)) (hu:∀ i y, y∈Metric.ball x R→‖q i y‖ ≤ w i)
  (funded:∀ᶠ n in atTop,Summable (fun i=>|v n i| * w i)) (hz: Summable (fun i=> |z i| * w i))
  (data:Tendsto (fun n=> ∑' i, |v n i-z i| * w i) atTop (nhds 0))
include hR hu

def transmit (q:ι→E→F) (v:ι→ℝ) (y:E):=∑' i, v i • q i y
lemma scaled_summable (v:ι→ℝ) (hE:Summable (fun i=>|v i| * w i)) (y)(hy:y∈Metric.ball x R): Summable fun i=>‖v i • q i y‖:=hE.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>by rw [norm_smul]; apply mul_le_mul_of_nonneg_left (hu i y hy) (abs_nonneg _))
lemma transmit_diff (h:ι→ℝ) (g:ι→ℝ) (hh:Summable (fun i=>|h i| *w i)) (hg:Summable (fun i=>|g i| * w i)) :
    transmit q h-transmit q g =ᶠ[𝓝 x] transmit q (h-g) := by
   filter_upwards [Metric.ball_mem_nhds x hR] with y hy
   unfold transmit
   haveI:=FiniteDimensional.complete ℂ F
   have he h (hh:Summable _) := Summable.of_norm (scaled_summable (q:=q) hR w hu h hh y hy)
   change _-_= ∑' i,(h i-g i) • q i y
   rw [← (he h hh).tsum_sub (he g hg)]; exact tsum_congr (fun j=>(sub_smul _ _ _).symm)

include hq
lemma amount (v:ι→ℝ)(hv:Summable (fun i=> |v i| *w i)): AnalyticAt ℂ (transmit q v) x:= by
  have ha i : Differentiable ℂ (q i) := (hq i).differentiable (by simp)
  apply Work.F02.analytic_series _ hR (fun i=> (ha _).const_smul _) hv
  intro k y hy; change ‖v k •q k y‖ ≤_; rw [norm_smul]; apply mul_le_mul_of_nonneg_left (hu k y hy) (abs_nonneg _)

include data hz funded in
set_option maxHeartbeats 1500000 in
lemma tracks : Tracks ∞ (fun n=>transmit q (v n)) (transmit q z) x:= by
  haveI:=FiniteDimensional.complete ℂ F
  have hA h ht := amount hR w q hq hu h ht
  have hT h ht : ContDiffAt ℝ ∞ (transmit q h) x:= ContDiffAt.of_le ((hA h ht).contDiffAt.restrict_scalars _) le_top
  refine ⟨funded.mono fun n hn=>hT _ hn,hT z hz,fun k hk=>tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  have hab i: 0≤ w i:= (norm_nonneg _).trans (hu i x (Metric.mem_ball_self hR))
  let W : (ContinuousMultilinearMap ℂ (fun _ : Fin k=> E) F) →L[ℝ] Tensor.T E F k := ContinuousMultilinearMap.restrictScalarsLinear ℝ
  let D := ‖W‖*expense R k
  have he (v : ι→ℝ) (i:ι) : ‖iteratedFDeriv ℝ k (fun y=>v i • q i y) x‖ ≤ D*(|v i| *w i):= (by
      have hh : ContDiff ℂ ω (fun y=>v i • q i y):=(hq i).const_smul _
      calc _ = ‖W (iteratedFDeriv ℂ k (fun y=>v i • q i y) x)‖ := congr_arg norm (hh.contDiffAt.of_le (show ↑k≤ω from le_top)|>.restrictScalars_iteratedFDeriv (𝕜:=ℝ) |>.symm)
           _ ≤ D * _ := ((W.le_opNorm _).trans (mul_le_mul_of_nonneg_left (costed _ hh hR (fun y hy=> by rw [norm_smul]; apply mul_le_mul_of_nonneg_left (hu i y hy) (by positivity)) _ _ (Metric.mem_ball_self (by positivity))) (norm_nonneg _))).trans_eq (by unfold D; simp [mul_assoc]))
  have hw (h:ι→ℝ) (ht:Summable (fun i=>|h i| *w i)) : ‖iteratedFDeriv ℝ k (transmit q h) x‖ ≤ D * ∑' i,|h i| * w i:=by
      have hh : HasSum (fun i=> iteratedFDeriv ℝ k (fun y=>h i • q i y) x) _:= CubicMatch.real_sum_terms k hR (fun i=> (hq i).const_smul (h i)) ht (fun i y hy=>by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hu i y hy) (abs_nonneg _))
      have hB := (ht.mul_left D).of_nonneg_of_le (fun _=>norm_nonneg _) (he h)
      exact (le_trans (hh.tsum_eq ▸ norm_tsum_le_tsum_norm hB) ((hB.tsum_le_tsum (he h) (ht.mul_left _)).trans_eq tsum_mul_left))
  apply squeeze_zero' (Eventually.of_forall fun _=> dist_nonneg) _ (by simpa only [mul_zero] using data.const_mul D)
  filter_upwards [funded] with n hn
  have hx i : |v n i-z i| *w i ≤ |v n i| *w i+ |z i| *w i:=by rw [←add_mul]; exact mul_le_mul_of_nonneg_right (abs_sub (v n i) (z i)) (hab i)
  have hh:=hw (v n-z) ((hn.add hz).of_nonneg_of_le (fun i=> mul_nonneg (abs_nonneg _) (hab i)) hx)
  rw [dist_eq_norm,← iteratedFDeriv_sub_apply ((hT _ hn).of_le hk) ((hT _ hz).of_le hk)]
  exact ((transmit_diff hR w q hu _ _ hn hz).iteratedFDeriv ℝ k |>.self_of_nhds) ▸ hh
end ink
end YM.Extension.UV.StationaryData
