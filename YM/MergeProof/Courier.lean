import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter

/-! # Change only the hard labels -/
set_option autoImplicit false
noncomputable section
namespace YM.Merge
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{n:Side}{s:Signed}{b:Site n}{X Y:Pipes G n}{d:Tap G n}
-- arbitrary Mates.X
variable {Z:Activities G n}
lemma courier (M:Z.Moves s b)(P:(X.pours d).Moves s b)(hx:Z.K=(X.pours d).K)(he:Z.forced=(X.pours d).forced)(q:Equiv.Perm ℕ)
   (hp:∀ i,X.softer (q i)=(X.softer i).image (affine s b)) (hf:∀ U i,d.logarithm (q i) U=d.logarithm i (pull s b U)):
   ∃ L:Progress.DirectedRecipe.Layout X s b,L.Follows d ∧ L.hard=M.kp:=by
  let T:(X.pours d).Moves s b:= ⟨P.ep,M.kp,P.reg_site,P.reg_support, (he ▸ M.forced_support : ∀ i, _), (he ▸ M.forced_inventory :∀ i,_), (he ▸ M.forced_tests :∀ i U,_),P.valuesE,(hx ▸ M.valuesK : ∀ i U,_)⟩ -- dep
  obtain ⟨L,h,hY,hz,hL⟩:= Progress.DirectedRecipe.Layout.from_raw T hp hf; exact ⟨L,hL,hY⟩
end YM.Merge
