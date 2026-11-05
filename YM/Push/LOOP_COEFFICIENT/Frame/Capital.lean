import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Ac.Table
import YM.Bid.Drops
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07

/-!
# Weighted-focus covariance, off shell (chart identities)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Matrix Filter Set Lattice Laurent Bloch RG Precision Exterior Pressure Wilson Gauge YM.Branch
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {P : Patch} {C : KernelChoices} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}


def weighing (P : Patch) (M : P.Points → G.Mat) := ∑ i : P.Points,P.weight i • M i

def central (P : Patch) (M : P.Frame G) := G.focus (weighing P (G.mat ∘ M))






def crownMap (P : Patch) (U : CoverConfig G) := (central P (P.selected U))⁻¹






variable [FiniteDimensional ℝ X] [CompleteSpace X] {U : X → CoverConfig G}


end YM.Push.Loops.Frames
