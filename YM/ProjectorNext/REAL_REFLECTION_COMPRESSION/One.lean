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
import YM.Ac.Table
import YM.Pressure.Seeds
import YM.Work.A07


set_option warningAsError false
/-!
# One-slot input for the anti-pair approximation

Keep precisely the common order. New port NOT assumed from `Makes`.
Possible production route: joint old/new density comparison at a fixed stop,
inserting bounded-real coarse stencil and pulling back along the same kernel;
see other modules. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror
open Set Filter Function MeasureTheory Cells Wilson Lattice Extraction
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G)

/-- Origin cutoff cylinder family. Use only under explicit
support/measurability/bound conditions; away from the needed order tails the
auxiliary cylinders can be padded. -/
abbrev Model := (N p : ℕ) → Config G (C.side N p) → ℂ

/-- Literal calibrated origin field, acting at cutoff `N,p`. -/
def source (v : C.book.Token) : Model C := fun _ _ => C.seen v 0















end YM.ProjectorNext.RMirror
