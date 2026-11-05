import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Bid.Fuels
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A15



/-!
# Four-dimensional fine annular measure and angular averages

On the real annulus itself, use Haar invariance under reflections for the
moments before radial integration. Lebesgue (not yet divided by `(2π)^4`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open MeasureTheory Measure Set Metric
open scoped Topology BigOperators InnerProductSpace ENNReal
variable {a b μ : ℝ} {F : Type*} [NormedAddCommGroup F]

def crown (a b : ℝ) := (fun x : E4 => ‖x‖) ⁻¹' Ioc a b






























end YM.Push.Loops
