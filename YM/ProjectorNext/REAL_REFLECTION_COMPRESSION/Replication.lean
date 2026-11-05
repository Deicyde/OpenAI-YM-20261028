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
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Fuels
import YM.Pressure.Rows
import YM.Work.A07
import YM.Work.B06

set_option warningAsError false

/-!
# Root of a pulled back cylinder

Keep all translations and site-mirror orientations of the centered link
tiling, not new local calibrations. Proof works also with complex plots,
with T.copy anti-linear under odd hand. Allows products on any subset.
No independence asserted except *conditionally* at disjoint cones.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror.Tower
open Set Filter Function MeasureTheory RG Wilson Lattice Cells 
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} (H : History G) {k l m p N : ℕ}

/-- The link-origin tilings to use *through* the same depth-k mesh. -/
abbrev floor (h : m ≤ k) (p : ℕ) : Tiling (H.S.side k p) := center H.S p h 0












end YM.ProjectorNext.RMirror.Tower
