import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
import YM.Next.RANK.Flux.Chronicle
import YM.Next.RANK.Odometer
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Rounds
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.CORRECTED_COLUMNS.Recover

/-!
# Retime the illumination and the muster. Keep the *step* in x prices

For the restarted Rank stretch, use an auxiliary recording temperature
whose coarse `temp` exactly matches output τ. Sectors won't see a
different *coarse* flag pattern. This doesn't adjust any StepData or
subtract any tallies from changing a Rep's kept-row indicators.
Fine `fiery` of the chart may still not be the physical τ_f
of the Rep so energy estimates & even membership comparisons need
careful checking. Use `crossfade` (ONLY late relative bounds) instead
of setting these equal. Compare  -- we follow a different
sufficient scheme keeping the paths and doing height replacements on
output & input Reps but not literally using all stencils/τ choices
of E with B = walls x.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Paint Filter Set
open scoped Topology BigOperators Classical
private lemma under_bulb (x : ℝ) (h : 1<x) : ContinuousOn temp (Set.Icc x (x^2)):=by
  intro i hi
  have hp : 1 < i := lt_of_lt_of_le h hi.1; have hs : i ≠ 0:= by linarith
  unfold temp; apply ContinuousAt.continuousWithinAt
  have ht := Real.continuous_exp.continuousAt.comp (x:=i) ((ContinuousAt.log (Real.continuousAt_log hs) (Real.log_pos hp).ne').pow 2)
  exact (Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.mpr (by linarith)).ne').mul ht

def retime (x : ℝ) : ℝ:= if h : ∃ i∈Set.Icc x (x^2), temp i=phase x then h.choose else x
lemma burst_limit : ∀ᶠ x in atTop, x ≤ retime x ∧ retime x ≤ x^2 ∧ temp (retime x)=phase x:= by
  have hu:= (tendsto_pow_atTop (α:=ℝ) (n:=2) (by norm_num)).eventually (Work.E09.temp_cost (1/8) (by norm_num))
  filter_upwards [phaseFit,hu,surge.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with x hx hh he hp
  have h0 : 0<x:= by linarith only [hp]
  have hs := alpha_phase x h0
  have hL : phase x ≤ temp x:= by
    rw [show regular x=temp x from (by simp [regular,temp,bill,Perch.boil,Perch.y,Vac.Numbers.Hat])] at hx; linarith only [hs,hx]
  have ht:temp (x^2)≤ Vac.Numbers.Hat x:=by
    refine hh.trans ?_; unfold Vac.Numbers.Hat; rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h0.le, ← Real.rpow_two, ← Real.rpow_mul h0.le]; apply Real.rpow_le_rpow_of_exponent_le hp.le; norm_num
  have hH := intermediate_value_Icc' (show x≤ x^2 by nlinarith only [hp]) (under_bulb x hp) (show phase x ∈ Set.Icc (temp (x^2)) (temp x) from ⟨ht.trans (le_mul_of_one_le_right ((Work.E04.temp_nonneg _).trans ht) he),hL⟩)
  have h : ∃ i∈ Set.Icc x (x^2), temp i=phase x:= hH
  unfold retime; rw [dif_pos h]; exact ⟨h.choose_spec.1.1,h.choose_spec.1.2,h.choose_spec.2⟩
lemma tall_limit : Tendsto retime atTop atTop := tendsto_atTop_mono' _ (burst_limit.mono (fun _ h=>h.1)) tendsto_id
lemma brims : ∀ᶠ x in atTop, radiusB x≤ radiusB (retime x) ∧ radiusB (retime x) ≤ 4*radiusB x:=by
  filter_upwards [burst_limit,eventually_gt_atTop (1:ℝ)] with x hx hv
  have ht:0<x:= by linarith only [hv]
  have hs:= lt_of_lt_of_le hv hx.1; have h0:0<retime x:= by linarith only [hs]
  refine ⟨Nat.ceil_le_ceil (pow_le_pow_left₀ (Real.log_pos hv).le (Real.log_le_log ht hx.1) _), Nat.ceil_le.mpr ?_⟩
  push_cast
  have h:=Real.log_le_log h0 hx.2.1; rw [Real.log_pow] at h; push_cast at h
  nlinarith only [pow_le_pow_left₀ (Real.log_pos hs).le h 2,show (Real.log x)^2 ≤ (radiusB x:ℝ) from Nat.le_ceil _]

lemma tone_ratio (d : ℝ) : Tendsto (fun x:ℝ=> phase (x+d)/phase x) atTop (𝓝 1):= by
  let f (y: ℝ):= (Real.log y)^((3:ℝ)/2)
  let g (y:ℝ):= y⁻¹*(3/2)*(Real.log y)^((3:ℝ)/2-1)
  have hf (x) (hx : 1≤x) : HasDerivWithinAt f (g x) (Set.Ici 1) x := (((Real.hasDerivAt_log (show x ≠ 0 by linarith)).rpow_const (Or.inr (by norm_num)))).hasDerivWithinAt
  have hg (x) (hx : x∈ Set.Ici 1): ‖g x‖ ≤ 2 := by
    change 1 ≤ x at hx; have ht : 0<x:= by linarith
    have he:= Real.log_le_sub_one_of_pos ht; have hl:=Real.log_nonneg hx
    let a:= Real.sqrt (Real.log x)
    unfold g; rw [Real.norm_of_nonneg (by positivity),show (3:ℝ)/2-1=1/2 by norm_num,←Real.sqrt_eq_rpow]; change _*a≤_
    have h': a ≤ x:= by nlinarith only [Real.sq_sqrt hl,hx,he,show 0≤a from Real.sqrt_nonneg _, show 0 ≤ x from ht.le]
    apply le_of_mul_le_mul_left _ ht
    rw [← mul_assoc,←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]; linarith only [h',ht]
  have huv : Tendsto (fun x:ℝ => x+d) atTop atTop:= tendsto_atTop_add_const_right _ _ tendsto_id
  have hl:=Real.tendsto_log_comp_add_sub_log d; have hb:=Real.tendsto_log_atTop
  have hh : Tendsto (fun x=> f (Real.log (x+d))-f (Real.log x)) atTop (𝓝 0) :=by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) ?_ (show Tendsto (fun x:ℝ=> 2* ‖Real.log (x+d)-Real.log x‖) atTop (𝓝 0) from by simpa using hl.norm.const_mul 2)
    filter_upwards [(hb.comp huv).eventually_ge_atTop 1,hb.eventually_ge_atTop 1] with x he hx
    exact (convex_Ici (𝕜:=ℝ) _).norm_image_sub_le_of_norm_hasDerivWithin_le (fun x h=> hf x h) hg hx he
  let W(t:ℝ) := Real.exp (f (Real.log (t+d))-f (Real.log t)-(Real.log (t+d)-Real.log t)/2)
  have ht : Tendsto W atTop (𝓝 1):= by
    have hv : Tendsto (fun x=> f (Real.log (x+d))-f (Real.log x)-(Real.log (x+d)-Real.log x)/2) atTop (𝓝 0):= by simpa using hh.sub (hl.div_const 2)
    simpa only [Function.comp_def,Real.exp_zero,W] using (Real.continuous_exp.tendsto 0).comp hv
  refine ht.congr' ?_
  filter_upwards [huv.eventually (eventually_gt_atTop 0),eventually_gt_atTop 0] with x hx hX
  have he (t) (ht : 0<t) : phase t=Real.exp (f (Real.log t)-Real.log t/2):= by
    unfold phase Vac.Numbers.Hat hot; rw [Real.exp_sub]; have hf:= Real.log_sqrt ht.le; rw [← hf,Real.exp_log (Real.sqrt_pos.mpr ht)]; unfold f Perch.y; ring
  change W _= _; rw [he (x+d) hx,he x hX,← Real.exp_sub]; unfold W; apply congr_arg; ring
lemma crossfade (G : Gauge) (L : Side) : ∀ᶠ x in atTop,
    let t:= phase (betaF G x L); let v:=fiery G (retime x) L
    0<t ∧ 0 < v ∧ v/2 ≤ t ∧ t ≤ 2*v:= by
  have hz:=tone_ratio (G.slopeConstant*Real.log L.val)
  have h':= (Work.E09.temp_ratio (G.slopeConstant*Real.log L.val)).comp tall_limit
  filter_upwards [burst_limit,hz.eventually (le_mem_nhds (show (3:ℝ)/4<1 by norm_num)),hz.eventually (ge_mem_nhds (show (1:ℝ)<5/4 by norm_num)),
    h'.eventually (le_mem_nhds (show (3:ℝ)/4<1 by norm_num)),h'.eventually (ge_mem_nhds (show (1:ℝ)<5/4 by norm_num)),(Work.E01.betaF_tendsto G L).eventually (eventually_gt_atTop 0),eventually_gt_atTop 0] with x h hh hv ha he hu hx
  intro t v;have ht:= alpha_phase _ hx
  have hV : temp (retime x)=phase x:= h.2.2
  change _ ≤ v / temp (retime x) at ha
  change v / temp (retime x) ≤ _ at he
  rw [hV,le_div_iff₀ ht] at ha; rw [hV,div_le_iff₀ ht] at he
  change _ ≤ t /phase x at hh; change t/phase x ≤ _ at hv
  rw [le_div_iff₀ ht] at hh; rw [div_le_iff₀ ht] at hv
  exact ⟨alpha_phase _ hu,by linarith only [ha,ht],by linarith only [he,hh,ht],by linarith only [hv,ht,ha]⟩
end YM.PhysicalNext.InteractingRank
