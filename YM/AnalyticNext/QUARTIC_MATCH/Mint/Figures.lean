import YM.AnalyticNext.QUARTIC_MATCH.Mint.Initially

/-!
# Address widths and price quotes

Caller can specify even further width requirements downstream *as attainable
narrower than these prices*. Not presupposing self-referential cap/delay
loop prices are justified. In `joint_prices` can quote after T, as needed.
Additional FLOOR to actually use the generated schedule. No silently changing
widths after a Roll.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Mint
open Filter Function Lattice Laurent Matrix RG RG.Supply Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Next Tree Joint BoxChain Mail Analyzers
open Progress.Joint Local Local.Budget Local.Rotate Local.Wages Hessian Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
namespace Affairs
variable {G : Gauge} {K : MapPrices} {L : KernelChoices} {P : Printed 2} {R : Printed 3}

structure Point (G : Gauge) (K : MapPrices) (P : Printed 2) (R : Printed 3) (i : ℕ) where
  s : ℝ
  C : ℝ
  rate : 0<s
  price : 0 ≤ C
  first : Entry G K i P s C
  δ : ℝ
  D : ℝ
  rateQ : 0<δ
  priceQ : 0 ≤ D
  second : AddOn G K i R s C δ D



structure SlotCharge (G : Gauge) (K : MapPrices) (L : KernelChoices) (P : Printed 2) (R : Printed 3) (j i : ℕ) where
  s : ℝ
  C : ℝ
  rate : 0<s
  price : 0 ≤ C
  B : ℝ
  positive : 0<B
  receives : Upcoming G K L j i P s B C
  δ : ℝ
  D : ℝ
  rateQ : 0<δ
  priceQ : 0 ≤ D
  E : ℝ
  positiveQ : 0<E
  hands : NextUp G K L j i R δ E s C D



structure Counters (G : Gauge) (K : MapPrices) (L : KernelChoices) (P : Printed 2) (R : Printed 3) where
  top i : Point G K P R i
  fromL j i : SlotCharge G K L P R j i



namespace Counters
variable (U : Counters G K L P R)


def bargain (r : Figures) : Figures where
  beginCost i := max (r.beginCost i) (max (U.top i).C (U.top i).D)
  classic j i := max (r.classic j i) (max (U.fromL j i).C (4*(U.fromL j i).D))
  pos i := (r.pos i).trans (le_max_left ..)
  pos_ij i j := (r.pos_ij i j).trans (le_max_left ..)

structure Focused (q : Quote) : Prop where
  draws : Designing K q
  starts i : q.widths.launch i ≤ min (U.top i).s (U.top i).δ
  receives j i : Adj j i → q.widths.emits j i ≤ min (U.fromL j i).s (U.fromL j i).δ
  bills i : max (U.top i).C (U.top i).D ≤ q.classicalCost.beginCost i
  awards j i : Adj j i → max (U.fromL j i).C (4*(U.fromL j i).D) ≤ q.classicalCost.classic j i






end Counters


end Affairs
end YM.AnalyticNext.QuarticMatch.Mint
