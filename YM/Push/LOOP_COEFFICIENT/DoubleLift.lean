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
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Pressure.Seeds
import YM.Work.A07
import YM.Work.B06

/-!
# Same-momentum two-leg Laurent lift for the quadratic precision

No tensor quotient postulate or assumption of exactness on one fixed torus.
First leg `q(-p)`, second `q(p)` in the matrix convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Lattice Laurent Bloch Exterior Complex Matrix
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator
variable {r s m : ℕ} {η C : ℝ}

abbrev Tape (r s : ℕ) := Momentum → Matrix (TypeFace r) (TypeFace s) ℂ

def dOut (X : Tape (r+1) s) (p : Momentum) := (symbol r (-p)).transpose * X p
def dIn (X : Tape r (s+1)) (p : Momentum) := X p * symbol s p











end YM.Push.Loops
