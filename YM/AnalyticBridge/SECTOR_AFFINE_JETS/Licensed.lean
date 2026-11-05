import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Next.FOUNDATIONS.SU2
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post
import YM.Push.FREE_RESOLVENT.Weights



/-!
# Use on actual selected Gaussian covariance and the cutoff predicates

Only take jets of the active kernels at the verified fields and their
coordinate neighborhoods with the Stored data fixed. Prove an anchored
derivative estimate even on the covariance of the probability integrals in
that notation (not interchanging derivatives without boundary conditions). In
the bookkeeping never assume perturbed V or variable Y,Z preserve allocation,
define the push identity with the licensed indicators.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
  
   
open  Matrix MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {F : Forest S.ratio} {A : Stores S} {x : ℝ} {k : S.Choices}





section application
variable {n : ℕ} {r v η d M l : ℝ} {V : Config G c}




end application

 

/-- Exact equality of the recorded output predicate. Needed also to authorize V
covariance tests. For actual portions, `Allocation` is used; the raw Plot read
is not an indicator partition. -/
def eligible (A : Stores S) (G : Gauge) (x : ℝ) := {V : Config G c | A.flags = RG.flags (temp x) V}






end YM.AnalyticBridge.SectorAffine
