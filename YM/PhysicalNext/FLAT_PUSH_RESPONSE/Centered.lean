import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Bid.Fuels
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06
import YM.Work.F05.Transport


/-!
# REAL push in tangent coordinates around the MATCH moving center

Smooth *interior* and no claim the probabilities themselves differentiate
when sectors cross. this part uses through PEAK (top Wilson antecedent); normalization later, here action
price on positive physical counting native sites. Real likelihood near the
branch will be recombined over all joint t later. Rotor shifts allow actual
Haar change of variables even before using the positive fraction near flat.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open Function Filter  Set Metric Asymptotics 
open RG Wilson Precision Lattice  Pressure Work.F05 Tree
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {G : Gauge} {m n : Side} {S : StepData m n}


variable (B : Forest S.ratio) (k : S.Choices) (p : Clip) (R : PathData G)
    (w : Bid.Dir G m) (u : Bid.Dir G m → AxisChart G B)

def home (x : ℝ) := exposure B (x • w) (u (x • w))





-- Identity for each given physical tag, same orientation.


variable {p R B u}
-- Lift virtual jets from generic coordinate fields, retaining the exact orientation


variable (R p B u)
-- Keep global formulas. Only effective on this ball.




variable {B p R u}
















-- all shift-domain masks will be at these coordinates




end YM.PhysicalNext.FlatResponse
