import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Next.FOUNDATIONS.SU2
import YM.Push.STATIONARY_UNIFORM.Paths

/-!
# Exact integral reorganization for the chosen collar

Tags removed ONLY on its support, where they yield identical predictions.
Everything else kept. Near-origin analytic task only. Does NOT assert
availability of small-field representation after push. Nor computes any
bulk coefficients in LABEL currency.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open Function Filter  Set Metric Asymptotics MeasureTheory 
open RG Wilson Precision Lattice  Pressure  Tree Matrix 
  
open scoped Matrix Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {m n : Side} (S : StepData m n)
def income (β : ℝ) (v : Bid.Dir G m) := S.push β (bare (G:=G) β) (represent v)
variable {S}

-- use t along w; interpretation fixed DECLARED stationary coupling coefficients
variable (B : Forest S.ratio) (k : S.Choices) (p : Clip) (R : PathData G)
    (w : Bid.Dir G m) (u : Bid.Dir G m → AxisChart G B)







variable {B p R u}





variable {η M m₀ K : ℝ} {P : ChartRatio G}






variable {W : B.Slice G → ℝ}

end YM.PhysicalNext.FlatResponse
