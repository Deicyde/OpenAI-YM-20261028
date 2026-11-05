import YM.AnalyticNext.QUARTIC_MATCH.Cells.Inside
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.LocalLedger
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Rainy
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment
import YM.Planned.STATIONARY_JET_PORT.AtHome

/-!
# Supply seam analyst on aux echo
 Volume POLY. Prepare thresholds after stage. Scalar relation transferred once with agreed chart, not another β book. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pane
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 
open       Planned.JetPort
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {c f : Side} {L : Side}
variable {σ C z u v a γ α m μ : ℝ} {j : ℕ}
section critical
variable {O : ChartRatio G} {S : StepData c f} {R : Tube G S} {F : Forest S.ratio} {r r' : Bid.Dir G c→AxisChart G F}
lemma payouts (h : r=ᶠ[𝓝 0] r') (he : ClassicalMatch F R.high R.low R.up R.down r) (hp : FiniteBound F R.up R.down R.high R.low α O r a γ u) :
    ClassicalMatch F R.high R.low R.up R.down r' ∧ FiniteBound F R.up R.down R.high R.low α O r' a γ u:= by
  constructor
  · intro j hj v
    let X (r : Bid.Dir G c→AxisChart G F) := (fun x : Bid.Dir G c=> tested F v R.high R.up x (r x))
    have hh: X r=ᶠ[𝓝 0] X r':= h.mono fun x hx=> congr_arg (tested F v R.high R.up x) hx
    obtain ⟨hK,hg,hV⟩:= he j hj v
    exact ⟨hK.congr_of_eventuallyEq hh.symm,hg, ((hh.iteratedFDeriv ℝ j).eq_of_nhds).symm.trans hV⟩
  have he t : thermal F t R.high R.up r O =ᶠ[𝓝 0] thermal F t R.high R.up r' O:= h.mono fun x hx=>by unfold thermal; rw [hx]
  obtain ⟨ha,hp,hs,hC⟩:= hp
  refine ⟨fun t=>?_,fun t=>(hp t).congr_of_eventuallyEq (he t).symm,hs,fun t i j σ τ hs ht=>?_⟩
  · filter_upwards [h,ha t] with x hx ha; rw [← hx]; exact ha
  change |_ - _|≤_
  rw [← ((he t).iteratedFDeriv ℝ 2).eq_of_nhds]; exact hC t i j σ τ hs ht
lemma fatten (hp : FiniteBound F R.up R.down R.high R.low α O r a γ u) (hk : a ≤ m) (hv:0 ≤ m) (hu:0 ≤ u) (hh : v ≤ γ) : FiniteBound F R.up R.down R.high R.low α O r m v u := by
  obtain ⟨h,h',hz,hl⟩:=hp; refine ⟨h,h',hz,fun t i j σ τ hs ht=>?_⟩; apply (hl t i j σ τ hs ht).trans
  apply mul_le_mul (mul_le_mul_of_nonneg_right ?_ hu) (Real.exp_monotone ?_) (Real.exp_pos _).le (by positivity); · gcongr
  gcongr
end critical
lemma coverBill (Y : Levels G) (m : ℕ) : 0≤Y.clock.loopCap m ∧ Y.clock.loopCap m ≤ 2* Y.clock.monitor m:= by
  have h:= Y.fits.thetaRange m; have ht:= Y.clock.adm m
  have hv : 1 ≤ Y.clock.monitor m:= Real.one_le_exp (sq_nonneg _)
  unfold Calendar.loopCap; refine ⟨by have hp := zero_le_one.trans hv; positivity,mul_le_mul_of_nonneg_left ?_ (by norm_num)⟩; exact (Real.rpow_le_rpow_of_exponent_le hv (h.2.trans (inv_le_one_of_one_le₀ (by exact_mod_cast show 1 ≤ _ from (le_trans (by decide : 1≤4) ht))))).trans_eq (Real.rpow_one _)
lemma brace (t : ℝ) (he : Real.exp 1 ≤ t) : 2*Vac.Numbers.P t ≤ ConnectedActivityE6.loopBill G L t:= by
  have hx:= Real.exp_pos 1; have hh := Real.log_le_log hx he; rw [Real.log_exp] at hh
  have ht : t ≤ betaF G t L:= le_add_of_nonneg_right (Work.E04.shift_nonneg _ _)
  have hs : 0≤ Real.log (Real.log t):=Real.log_nonneg hh
  unfold ConnectedActivityE6.loopBill Delay.fineMonitor Vac.Numbers.P; gcongr; exact hx.trans_le he
end YM.PhysicalNext.Repeat.Pane
