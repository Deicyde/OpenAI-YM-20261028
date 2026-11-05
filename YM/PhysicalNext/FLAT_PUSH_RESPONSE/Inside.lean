import Mathlib.MeasureTheory.Measure.Tilted
import YM.Next.FOUNDATIONS.SU2
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Pocket
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Sieve
import YM.Push.STATIONARY_UNIFORM.Paths

/-!
# Issuing the genuine chart-pocket leading and Hess tickets

Fixed-period after shifted integration and scaling (here not stage hats).
Need supplements for other fields; see Fade. Before normalized/thermal
results; `IncomeRay` includes actual derivatives on THE contributor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open Function Filter WilsonStartup.Change Set Metric Asymptotics MeasureTheory Next.SectorChange.Gaussian
open RG Wilson Precision Lattice  Pressure Work.F05 Tree Matrix 
  
open scoped Matrix Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {m n : Side} {S : StepData m n} {B : Forest S.ratio}
    (k : S.Choices) {u : Bid.Dir G m → AxisChart G B} {p : Clip} {R : PathData G}
    {P : ChartRatio G} (w : Bid.Dir G m) {r M b c : ℝ}

-- allow common rechoice to W: needs regular on the CLOSED pocket picked
-- before actual exterior application but AFTER fixing real period.



-- at 0 only Hess of the real pushed numerator; DerivExist is important
-- for differentiating a later physical expense.
structure IncomeRay (D : ℝ→ℝ→ℝ) (x y z : ℝ) : Prop where
  grad (g : ℝ) : DifferentiableAt ℝ (deriv (D g)) 0
  dot (g : ℝ) : ∀ᶠ x in 𝓝 0,DifferentiableAt ℝ (D g) x
  cost : Tendsto (fun g => D g 0) vacWay (𝓝 x)
  mask : Tendsto (fun g => deriv (D g) 0) vacWay (𝓝 y)
  price : Tendsto (fun g=> accel (D g) 0) vacWay (𝓝 z)



end YM.PhysicalNext.FlatResponse
