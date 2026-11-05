import YM.AnalyticNext.CUBIC_MATCH.Ledger.Figures
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Pre
import YM.Progress.STATIONARY_SCENES.Dispatch


/-!
# Required budget positions on the Iteration sheet

Phase incoming, width outgoing; even compare widths with a half-width
reserve. Fees here BEFORE subtraction margin (`Room` separately). `Arrange`
shows availability simultaneous with the IterationRecipe prices on its route
(order independent of L and period). Can also use on other routes by proving
`Booked` on those sheets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GradedCube

open Function Lattice RG RG.Supply Wilson Precision Bid Progress.StationaryScenes
open CubicMatch CubicMatch.Ledger Next.Scheduling Extra.Iteration
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

structure Booked (S : Sheet G) (K : MapPrices) (B : ClassicalCosts) : Prop where
  landing j i : Adj j i → (S.profile i).width ≤ (ticket G K j i).σ / 2
  start j : initialBill G K (S.profile j).clip.direct j ≤ B.top j
  step j i : Adj j i → stageFee G K (S.profile j).clip.direct (S.profile i).clip.direct S.kernel.penalty j i ≤ B.fresh j i
  phase j i L : Adj j i → S.floorL j ≤ L.val → surplus K j i * tilt L ≤ (S.profile j).width / 2

variable {S : Sheet G} {D : Rolls S} {Q : PostCost D} {a : Levels G} {H : Horizon a}
    {K : MapPrices} {B : ClassicalCosts}

namespace Booked
variable (h : Booked S K B) (C : Service a K Q H)
include h C







end Booked
end YM.Primitives.GradedCube
