import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Installation
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Kettle
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Yield



/-!
# Translating Bills & time of funding

Convert OnBand & support budgets; toward Directed consumption as an API keeping
these Arms. Consumers have their own named existential κ at B. Use ANY positive instance
carrying official point charge; don't claim arbitrary projections of independent calls unify.
Keep delays and purchased conditions explicit. Need apply even when witness (a,M) handed onward.
No attempt to build Directed supplies here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Due
open Function Lattice RG Precision Wilson Pressure Pressure.Stores MeasureTheory Push.SectorMeasure
open Matrix Push.SectorMeasure.Oriented Push.AbsoluteSums Tree Next.Fluctuations Filter Win Win.Promise Finset
open Centered Aff Aff.Mint Wages Jewels   Mixed Work.E03 Exterior Bloch Turn   Packets
open YM.Progress.StationaryScenes YM.Input Pressure.Testing RG.Supply RG.Shoot Cab
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge}

-- receive Sworn matching dictionary even if elsewhere came another E
section
variable {C : Sheet G} {D : Rolls C} {Θ : Protection D} {W : Supply.Delays Θ}
  {Y : Bar W} {I : Wait Y} {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P)




end

-- Fits and finances known at pre/post-L. Admissions given in canonical points use Stage equality explicit.
lemma carriage (a : Levels G) (m p : ℕ) :
    a.clock.hatBeta (m+1)=betaF G (a.clock.hatBeta m) ((a.clock.op m p).patch.L) := by
  unfold Calendar.hatBeta betaF; rw [Schedule.scale_succ]; change _=_+_ * Real.log (a.clock.schedule.block m).val; ring



lemma post_goods (G : Gauge) (D : Patch) : ∀ᶠ x in atTop, 0 < x ∧
    ∀ (a : Levels G) (m p : ℕ), (a.clock.op m p).patch=D → a.clock.hatBeta m=x →
      let q:=a.clock; let u := q.hatBeta (m+1)
      q.loopCap (m+1) ≤ (u ^ (1/8:ℝ)) ∧ q.allowance (m+1)≤ amend G D x (1/2) ∧
        q.forcedAllowance (m+1) ≤ amend G D x (1/2) ∧ (a.budget (m+1)).B ≤ 2*radiusB x := by
  filter_upwards [Fees.growth G D.L (show (0:ℝ)<1/8 by norm_num) (show 0 ≤ (2:ℝ) by norm_num) 1 0,
    Fees.hat_decay G D.L zero_lt_one (show 0<(1/5:ℝ) by norm_num) (show 0 < (1/2:ℝ) by norm_num),
    Fees.horizons G D.L 125 zero_lt_one (le_refl (0:ℝ)) (show 2*1 < (3:ℝ) by norm_num), eventually_gt_atTop (0:ℝ)]
    with x hx hp hw hv
  refine ⟨hv,fun a m p H hr => ?_⟩
  intro q u; let L := a.clock.monitor (m+1)
  have he : u=betaF G x D.L := by rw [← H,← hr,← carriage]
  have ht : L=Delay.fineMonitor G D.L x := by unfold Delay.fineMonitor L Calendar.monitor; rw [carriage a m p,hr,H]; rfl
  have hu : 0<u := zero_lt_one.trans (a.fits.delayed _)
  have hi : 1≤L := Real.one_le_exp (by positivity)
  have hv : (1:ℝ) ≤ a.clock.J (m+1) := by exact_mod_cast (Nat.le_trans (by decide : (1:ℕ)≤4) (a.clock.adm _))
  constructor
  · unfold Calendar.loopCap
    have hu : q.theta (q.J (m+1)) ≤ 1 := (a.fits.thetaRange _).2.trans (inv_le_one_of_one_le₀ hv)
    simp only [he]
    simp only [pow_zero, mul_one, ← ht] at hx
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hi hu) (show (0:ℝ)≤2 by norm_num)).trans hx
  constructor
  · let v := q.hatCoupling (m+1); have h' : v ≤ 1 := by
      apply inv_le_one_of_one_le₀; exact (Real.sqrt_one.symm ▸ Real.sqrt_le_sqrt (a.fits.delayed (m+1)).le) -- fix cast
    unfold amend; rw [← he]; unfold Calendar.allowance; change v ^ _ ≤ _
    refine le_trans (Real.rpow_le_rpow_of_exponent_ge (show 0<v from inv_pos.mpr (Real.sqrt_pos.mpr hu)) h' (show (2:ℝ) ≤ 11/5 by norm_num)) ?_
    have hs := (βhunt u hu).2
    rw [Real.rpow_two]; apply le_of_mul_le_mul_left _ hu; change u*v^2≤_; rw [show u*v^2=1 from hs]
    apply le_trans _ (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (a.fits.delayed _).le (show (-1:ℝ) ≤-(1/2) by norm_num)) hu.le)
    rw [Real.rpow_neg_one,mul_inv_cancel₀ hu.ne']
  refine ⟨?_,?_⟩
  · unfold Calendar.forcedAllowance; unfold q; rw [show a.clock.monitor _=_ from ht]; simpa only [neg_mul,one_mul,amend] using hp
  change radiusB u ≤ 2*radiusB x
  rw [he]
  exact hw.2.1

-- translate incoming Leg. No top loop purchase here outside a's genuine cap.

end YM.AnalyticNext.ConnectedActivity.Due
