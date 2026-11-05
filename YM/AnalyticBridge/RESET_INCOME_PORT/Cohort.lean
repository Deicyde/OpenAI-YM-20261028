import YM.AnalyticBridge.RESET_INCOME_PORT.HeadGas
import YM.AnalyticBridge.RESET_INCOME_PORT.LogMotion

set_option warningAsError false

/-!
# Calibrate regenerated signed gas head (two-probe version)

When a log forecast for the INTEGRATED atoms (not just d.flight)
is what's available from local estimates. Allows paired pieces NOT
individually cheap on final currency. Handles legitimate log through this
estimate as well and buys the desired value precision. This path doesn't
attempt to earn full Prereset EBound. Still entirely conditional on
`HeadGas` & all these forecasting and price inputs in the chosen sector
reorganization. No assumption proofs involving only origins of `Atoms`
apply afterwards through variation, projections etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange UVNext.CouplingReset Input RG.Supply RG.Shoot Pressure.Testing
open SectorNext.Vacuum.ReLog LogMotion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {e : Plate G S} {R : Rep G f} {V : Config G c} {κ δ u : ℝ}

namespace HeadGas
/-- In a comparison with a *known* gas (atoms `aim` at this point).
No change in the bookkeeping if they are vastly different as long as
both+envelope are actually paid. Origin must stay the same. Assessment
includes the common flight, scalar and real prediction error compiled in
local pressure reads (including every joint address). `room` is the residual
estimator and `fund` must pay *even the enlarged* absolute envelope. -/
structure Cohort (c : Side) where
  cost : Grid (Site c)  -- expected costs to be prepared for predictor
  compare : Grid (Site c)  -- |local difference| vs comparison *log*
  token : Token
  early : ℕ → ℝ
  aim : ℕ → ℝ  -- approximation of an atom here
  each : ℝ -- cap on support hits of compare
  χ : ℝ

namespace Cohort
variable (d : HeadGas e) (k : Cohort c)

structure Serves (R : Rep G f) (V : Config G c) (u δ : ℝ) : Prop where
  knows i : (d.reads i).Nonempty
  roots : d.Balance R V
  fund : Fund d.reads e.point.B k.token.width k.token.quota k.token.rate k.token.wages
  reserve : 0≤k.χ
  localAtom i : Chip k.χ (d.atoms i V) (k.aim i) (k.early i) (k.token.wages i)
  cost_empty : k.cost ∅=0
  clears : k.compare ∅=0
  tests (i : Support c) : |locker (fumes d.reads k.aim) i - k.cost i| ≤ k.compare i
  hit x : ∑ i ∈ (Finset.univ : Finset (Support c)).filter (fun i=>x∈i), k.compare i ≤ k.each
  room : |e.outside R V + d.flight V-u -∑ i,k.cost i| + sites c*(k.token.quota*k.χ+k.each) ≤ δ/2






end Cohort
end HeadGas
end YM.AnalyticBridge.ResetIncome
