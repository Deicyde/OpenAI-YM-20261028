import YM.RemainderComparison.Cadenza.Troves
import YM.RemainderComparison.Ethereal.Crest
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Currency
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadenza
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Funk Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {P:Teller G} {Q:ConnectedActivityE6.Target G P} {p:Patch} {L : Side} {K:KernelChoices} {j n r : ℕ}
variable {q o w : ℝ→ℝ}{W μ:ℝ} {A:ConnectedActivityE6.Target.Order G W}
open Ethereal Geo
namespace Tuba
-- budget for all post after Φ transitions.Flag rare. Compute.Hoard
variable (G) (S:RG.Stage)
open Time Residual
variable {A':ℝ}

lemma surf {p:BudgetPoint} (h: Same S p)(hH:0 ≤ A') : Ethereal.foam G p A' ≤ Ethereal.foam G (Time.probe S) 1*(1+p.B)^(4:ℕ) * A':=by
  have he : resetLoss G p = resetLoss G (Time.probe S) := by
    unfold resetLoss Residual.multiplier VerifiedReset.pairBill Time.probe; dsimp; rw [h.1,h.2.1]
  have ht := loss_pos G p
  have hw : 0 ≤ 1 - Real.exp (-(1/2:ℝ)) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  unfold foam Footprint.payment Footprint.degreeIncome
  rw [h.2.2,← he]; dsimp only [Time.probe]
  let D := Real.exp ((S.supportExponent+1)*81)*resetLoss G p * ((1/2:ℝ)⁻¹^ (4:ℕ) * ↑(4:ℕ).factorial * Real.exp (1/2))*(1-Real.exp (-(1/2)))⁻¹
  have hd : 0 ≤ D := by unfold D; positivity
  calc
    _ = D*Footprint.spread 1 (4*p.B+2)*A' := by unfold D; ring
    _ ≤ D*(Footprint.spread 1 (4*1+2)*(1+p.B)^ (4:ℕ))*A' := by
      gcongr D*?_ * A'
      unfold Footprint.spread Animals.ballCost; push_cast; rw [one_mul,show (28561:ℝ)=13^4 by norm_num,← mul_pow]
      gcongr; linarith
    _ = _ := by dsimp only [D]; ring

def swell := foam G (Time.probe S) 1 + ((2:ℝ)+2⁻¹ * pairBill G (Time.probe S)) *lowHard (Time.probe S) S.clip S.width S.paths
lemma inn :0≤foam G (Time.probe S) 1:=by
   unfold foam Footprint.payment Footprint.degreeIncome; have ht:=loss_pos G (Time.probe S); have hp:0 ≤ 1- Real.exp (-(1/2:ℝ)):= by rw [sub_nonneg]; apply Real.exp_le_one_iff.mpr; norm_num
   positivity
lemma shore : 0≤ swell G S:=by
   have hv:= inn G S; have ht := pair_nonneg G (Time.probe S); have hp := (budget_pos (Time.probe S) G S.clip S.width_pos S.paths_pos.le).2.2; unfold Tuba.swell; positivity
lemma coast {p:BudgetPoint} (h:Time.Same S p) {H:ℝ}(hH:0≤H)(ht:H≤p.threshold^2): Ethereal.ocean G p S.clip S.width S.paths 0 H ≤ swell G S * (1+p.B)^(4:ℕ)*p.threshold:=by
    have he : pairBill G p = pairBill G (Time.probe S) := by unfold VerifiedReset.pairBill Time.probe; dsimp only []; rw [h.1,h.2.1] -- notation
    have hp:=p.threshold_pos; have hx:=p.threshold_le; have hz:= pair_nonneg G p
    have hy : 0 ≤ hitNeed p G 0 H :=by unfold hitNeed; positivity
    have hr := (budget_pos (Time.probe S) G S.clip S.width_pos S.paths_pos.le).2.2
    have hh:= inn G S
    have hu : H ≤ p.threshold:=by nlinarith
    have hm : hitNeed p G 0 H ≤ ((2:ℝ)+2⁻¹*pairBill G (Time.probe S))*p.threshold:=by rw [hitNeed, ← he,abs_zero]; linarith only [mul_le_mul_of_nonneg_right hu hz,mul_le_mul_of_nonneg_right (div_le_one_of_le₀ ht (sq_nonneg _)) hp.le]
    exact (add_le_add ((surf G S h hH).trans (mul_le_mul_of_nonneg_left hu (by positivity))) (mul_le_mul hm (lowSoft_exp S h) (budget_pos p G S.clip S.width_pos S.paths_pos.le).2.2 (hy.trans hm))).trans_eq (by unfold Tuba.swell; ring)

lemma rhythm (L:Side) : ∀ᶠ x:ℝ in atTop,0 < gStep (betaF G x L) ∧ gStep (betaF G x L)≤ Pressure.temp x:=by
    filter_upwards [eventually_gt_atTop (1:ℝ), Delay.shift_pos G L] with x hx h; have he : x≤ betaF G x L:= le_add_of_nonneg_right (Work.E04.shift_nonneg G L); have hz: 0<x:=zero_lt_one.trans hx
    refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr h),?_⟩
    exact (inv_anti₀ (Real.sqrt_pos.mpr hz) (Real.sqrt_le_sqrt he)).trans (le_mul_of_one_le_right (inv_pos.mpr (Real.sqrt_pos.mpr hz)).le (Real.one_le_exp (sq_nonneg _))) -- implicit

lemma shelling (L:Side) : ∀ᶠ x:ℝ in atTop,∀ Z:BudgetPoint,Temper Z S x G L → (S.clip.direct ≤ 1→ WilsonStartup.Decent S.clip Z)∧ Geo.Width Z S.clip S.width:=by
    have hh:= ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp Work.E01.radiusB_tendsto|>.const_mul_atTop S.width_pos).eventually_ge_atTop (4*(S.supportExponent+1))
    filter_upwards [eventually_gt_atTop (0:ℝ),hh,Work.E01.radiusB_tendsto.eventually_ge_atTop 2, Real.tendsto_log_atTop.eventually (WilsonStartup.Timing.cut S.clip)] with x hx ht he h Z hZ
    have hB : Z.B=WilsonStartup.Timing.balls (Real.log x):= hZ.pose; have hv : Z.threshold= WilsonStartup.Timing.temp (Real.log x):=by rw [hZ.pressure, (Time.threshold_aligned x hx).2, (Time.threshold_aligned x hx).1]; rfl
    refine ⟨fun h'=> ⟨h',hZ.pose.symm ▸ he,hB.symm ▸ hv.symm ▸ h⟩, S.width_pos,S.slow_selector,(div_le_iff₀ (show (0:ℝ)< (Z.B:ℝ) from Nat.cast_pos.mpr Z.B_pos)).2 ?_⟩
    rw [hZ.salary,hZ.pose]; change 4*(S.supportExponent+1)≤ S.width*(radiusB x:ℝ) at ht; linarith only [ht]

end Tuba
end YM.RemainderComparison.Cadenza
