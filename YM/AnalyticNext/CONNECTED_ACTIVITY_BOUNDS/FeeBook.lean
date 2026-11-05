import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Bearer
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Halls
import YM.Push.ABSOLUTE_SUMS.Buy

/-!
# Post-L theorem: all common-sector fees on the natural amplitudes

Combining the arguments of `AbsoluteSums.Buy.sectors` with same
witnesses, `PointCharge` (from the grant producer, kept for actual use
on tilted orientations and with SectorMeasure, not an abstract cap on
completed `connected` coefficients). Needed eventually in x under pinned
scale arguments. This version calls one step sale order at a time; finite
lists of such calls may use same pre/post floors. Reserves are purchase
*before-L* for inherited support, at pointed ord in dPrice. Preserve R
thresholds independent of β shooting in this use. No request for funding
the outgoing multipliers except via Aff `Funds` and prices proven here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Cab
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths Chains Calls Mixed
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

-- spendSeed in quote same order all gates. ExtraSeed chosen 0 (charged on
-- actual covers separately). q=1/2 implied for power tail.
def chosen (S : StepData c f) (x β : ℝ) (G : Gauge) (a δ ε κ : ℝ) (ρ : Tempo) :=
    Buy.quote G S.patch.L κ (1/4) a ε δ β x 1 0 (5*tab G S.patch x^7) (constant*amend G S.patch x ρ.rate)

def PackCost (S : StepData c f) (b : Costs) (p : Stores S) := Packets.income b.cap b.spendSeed b.gain p.shares

structure FeeBook (T : Tube G S) (x W r : ℝ) (R : Rep G f) (N : ChartRatio G) (b : Costs) : Prop where
  sign : 0<R.beta
  bought : Costs.Buy b S.patch.L 500 (radiusB x)
  ledger : ∃ (q : Promise) (X : Turns) (_h : X.exp_width ≤ q.alpha), Frisk T x q X ∧ X.pace (paceR x) < 1 ∧
    ∃ w, Token T x r (takePaid X) w (fun _ L _ Y z => other T x W R N L Y z) (pOther T x R) b.head
      b.optionalHit (takePaid X).expense
  pach : ∀ (F : Forest S.ratio) (A p : Stores S) (Y : Mint T F A x), cert S x A Y.V → Y.r=r →
      Y.u=holdSize G S.patch x → Installed p A (450*radiusB x) → ∀ Z L,
        |pact p R.activities L R.beta W N Y Z| ≤ PackCost S b p

-- same buy on any accumulation of covers (before actual exponent grouping). `prach ε` needed separately.


-- post, hypotheses pre quotations remain for actual joint Letter buy.

end YM.AnalyticNext.ConnectedActivity.Cab
