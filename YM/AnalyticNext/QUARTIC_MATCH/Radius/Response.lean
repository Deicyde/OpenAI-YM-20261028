import YM.AnalyticNext.QUARTIC_MATCH.Radius.Polish
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Push.PRICE_COMPILER.Authors

/-!
# Extract the leading branch derivative out of graded charges

Useful for *non-ell2 sup* estimate with exponential weight on each chart source.
Doesn't require redundant derivative price of same order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Analysis Estimate Estimate.Purse Polish
open scoped Topology ContDiff BigOperators
section
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable {P : Ticket X} {Q : Ticket Y} {x : X} {f : X→Y} {g : Y→Z} {d : Z} {C D' : ℝ}

def expected (m : ℕ) (C D : ℝ) := 2^m * (indexed m (fun k => Polish.counted k)*D * C * D^m)



end
end YM.AnalyticNext.QuarticMatch.Radius
