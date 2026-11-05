import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Numerics
import YM.Push.SECTOR_MEASURE.Presented


/-!
# The input presented to this service

One transition, including any in-budget band-continuous input
(`advance` query). Intact Alloc columns use exactly THESE paths and
weights. PointCharge supplied by RGrants, not from any conjectured
path-to-V action estimates. Caps rounded only in the hypothesis for
prices, no adjustment to actual R.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Lattice RG Pressure Pressure.Stores RG.Patch Wilson
open Push.SectorMeasure Presented Push.AbsoluteSums Reserves
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}

/-- E bills on the **fine** lists. -/
def incomingE (G : Gauge) (L : Side) (x : ℝ) := (Real.sqrt (betaF G x L))⁻¹ ^ ((11:ℝ)/5)
def incomingK (G : Gauge) (L : Side) (x : ℝ) := Real.exp (- ((Delay.fineMonitor G L x) ^ ((1:ℝ)/5)))
def loopBill (G : Gauge) (L : Side) (x : ℝ) := 2 * Delay.fineMonitor G L x

lemma incomingE_rate (G : Gauge) (L : Side) : Rate G L (-(11/10)) (incomingE G L) := by
  refine Rate.power.congr ?_
  filter_upwards [Delay.shift_pos G L] with x hx
  unfold incomingE
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le, ← Real.rpow_mul hx.le]; congr 1; norm_num

lemma incomingK_rate (G : Gauge) (L : Side) (a : ℝ) : Rate G L a (incomingK G L) := by
  have he := Rate.monitor_cutoff (G:=G) (L:=L) (a:=a) (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/5)
  simpa only [neg_mul,one_mul] using! he

lemma loopBill_rate (G : Gauge) (L : Side) : Rate G L 0 (loopBill G L) := Rate.monitor.mul_left _

/-- Concrete sufficient input (require the same old PathData at applications
of Funds, calibration etc. and post-L clock conditions where used).
PosDef, Guessed etc. needed on stationary data later use their own clauses. -/
structure Intake (P : Teller G) (T : Tube G S) (x : ℝ) (R : Rep G f) : Prop where
  ready : P.Funds S T
  received : Presented.Fits T R x
  cap : R.Lawful P.top.width P.top.paths (loopBill G S.patch.L x) (incomingE G S.patch.L x) (incomingK G S.patch.L x)
  exponent : P.top.supportExponent = R.p.supportExponent
  height : 1 < betaF G x S.patch.L
  sizes : R.p.B = radiusB (betaF G x S.patch.L)
  window : betaF G x S.patch.L / 2 ≤ R.beta ∧ R.beta ≤ 2 * betaF G x S.patch.L

namespace Intake
variable {x W κ : ℝ} {P : Teller G} {R : Rep G f}

lemma positive (h : Intake P T x R) : 0 < R.beta := (half_pos (zero_lt_one.trans h.height)).trans_le h.window.1

/-- Work WITHOUT altering the sector allocation or the scalar weights. -/
lemma allocation (h : Intake P T x R) (hp : PointCharge T x W κ) :
    Charged T x W κ ∧ ∀ (F : Tree.Forest S.ratio) (A : Allocation G S x W), Presented.PortionCost A F T κ R :=
  ⟨hp.charged h.ready, fun F A => portionCost hp h.ready h.cap h.positive.le h.received F A⟩
end Intake

namespace Application
open Pressure.Testing RG.Supply RG.Shoot Precision YM.Input
variable {C : Sheet G} {D : Rolls C} {Θ : Protection D} {W : Supply.Delays Θ}
variable {Y : Bar W} {I : Wait Y} {Z : ChartRatio G} {K : MapPrices} {Q : PostCost D}

lemma clock_next (B : Levels G) (m p : ℕ) :
    B.clock.hatBeta (m+1)=betaF G (B.clock.hatBeta m) (B.clock.op m p).patch.L := by
  unfold Calendar.hatBeta betaF
  rw [Schedule.scale_succ]; change _ = _ + _ * Real.log (B.S.block m).val; unfold Levels.S; ring

lemma intake_at (B : Directed G I Z K Q) (N m p : ℕ) (hm : m < N) (R : Rep G (B.a.S.side (m+1) p))
    (hL : Lives B.bake N (m+1) p R) (hB : R.beta ∈ band B.a (m+1)) :
    let i := B.a.clock.J m; let j := B.a.clock.J (m+1); let T := ships B N m p
    Intake (query C K j i) T (B.a.clock.hatBeta m) R := by
  intro i j T
  let t := B.a.clock
  let S := t.op m p
  let x := t.hatBeta m
  have he := clock_next B.a m p
  change t.hatBeta (m+1) = betaF G x S.patch.L at he
  have hh : (B.a.params (m+1)) = C.profile j := congr_fun B.valid.stage _
  refine ⟨proceeds B N m p hm,⟨?_,?_,?_⟩,?_,?_,he ▸ (B.a.fits.delayed (m+1)), ?_,?_⟩
  · rw [hL.path, B.bases]; rfl
  · exact hL.clip
  · change _=temp _
    rw [hL.point]; change t.threshold (m+1)=temp (betaF G x S.patch.L); rw [← he]; rfl
  · have hU : incomingK G S.patch.L x=t.forcedAllowance (m+1) := by
      unfold incomingK Delay.fineMonitor; rw [← he]; rfl
    have hF : incomingE G S.patch.L x=t.allowance (m+1) := by unfold incomingE; rw [← he]; rfl
    have hg : t.loopCap (m+1) ≤ loopBill G S.patch.L x := by
      unfold Calendar.loopCap loopBill Delay.fineMonitor; rw [← he]
      have he' := t.adm (m+1)
      have ht := B.a.fits.thetaRange (m+1)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [show Vac.Numbers.P (t.hatBeta (m+1)) = (t.monitor (m+1)) ^ (1:ℝ) by rw [Real.rpow_one]; rfl]
      apply Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _))
      refine ht.2.trans (inv_le_one_of_one_le₀ ?_)
      exact_mod_cast show 1 ≤ t.J (m+1) by omega
    refine ⟨?_,hU.symm ▸ hF.symm ▸ hL.valid.labels⟩
    change R.path.Bounds R.clip (C.profile j).width (C.profile j).paths (loopBill G S.patch.L x)
    rw [← hh]; exact { hL.valid.paths with two := budget_loosen hL.valid.paths.two hg }
  · rw [hL.point]; change (C.profile j).supportExponent=(B.a.params (m+1)).supportExponent; rw [hh]
  · rw [hL.point]; change t.coverSize (m+1) = radiusB (betaF G x S.patch.L); rw [← he]; rfl
  change betaF G x S.patch.L / 2 ≤ _ ∧ R.beta ≤ 2*betaF G x S.patch.L; rw [← he]; exact hB
end Application
end YM.ConnectedActivityE6
