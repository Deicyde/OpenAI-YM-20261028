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
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Work.A07
import YM.Work.B06

set_option warningAsError false

/-!
# Actual matched-coarse candidate (*choice of coordinates* red)

Use the same opening norm, mask threshold scaling and primary section as for
O. Bound on the ENTIRE group cylinder using the compact cover readout; no
health screen in this bound! (The health-screen bound from priced does
something different.) Native r uniform in k & p, hence has all the support
growth receipts from UV_STRESS for backward queries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PhaseCoarse
open Function Filter Set MeasureTheory Analysis Extraction Lattice RG Wilson Overlay Marker Cells  Source
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {N p h k m d : ℕ}








def cylinder (k p d : ℕ) (z : C.label d) : Config G (C.side k p) → ℂ :=
    Source.initial (C.localSection d) C.path k p z 0

def dye (k p d : ℕ) (z : C.label d) (V : Config G (C.side k p)) := (cylinder C k p d z V).re












end YM.UVNext.PhaseCoarse
