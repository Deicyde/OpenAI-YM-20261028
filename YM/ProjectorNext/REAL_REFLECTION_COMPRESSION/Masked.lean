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
import YM.Ac.Table
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06




set_option warningAsError false

/-!
# A variant of Grid.MatchAt (--) using bounded-masked
rather than polynomial approximants

Criterion/B05/Grill use bounded Borel cylinders. The fine Wilson field
`source` we are trying to approximate does **not** change; nothing here
removes the forced K's from its propagated mass. But insert at a coarser
level an actual *masked* multiple of the reference stencil, congruent with
its unmasked values on the healthy inputs, zero remainder. This simplifies
an otherwise difficult joint birth problem (would have to attach and price
failed-mask complements for the new source). Preserves reality/signed action,
support and unit. Requires budgeting this new source from the same vac.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror.Masked
open Set Filter Function MeasureTheory RG Wilson Lattice Cells  Extraction  Labels Source
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} (C : Family G) {n : Side} {k l m p N d : ℕ}

abbrev R (d : ℕ) := C.labels.level d
abbrev reach (o : Site n) (d : ℕ) := (C.localSection d).footprint o

def payload (B : BudgetPoint) (u : C.label d) (o : Site n) : Config G n → ℂ :=
    (C.localSection d).places ((R C d).scaled B.threshold⁻¹ ((R C d).core u)) o








section symmetry















end symmetry



def size (d : ℕ) : ℕ := (C.localSection d).stencil.sup fun x => Finset.univ.sup fun a : Axis => (x a).natAbs






end YM.ProjectorNext.RMirror.Masked
