import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-! Packet use with separate address caps. No assumption of global positivity
of interacted density or sums/products; e.g. allows bounded ancillary real log or
likelihood price for each typed address in the component. Only on real integrated
branches: don't apply estimates after stripping a constraint that forces the actual
seed prerequisites.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial    Metric   Exterior Bloch 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical  ContDiff ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f} {x W K : ℝ}

/-- Attach whole-list prices, for each occurrence with projected anchor X in a
packet halo. Allow multiplicity *per anchor* (replace this if using an invoice
from absolute counting, e.g. buy any finite sum of such polynomial costs). -/
structure Register {ι : Type} (s : Finset ι) (u : ι → Site c) (O : Stores S) (D x k : ℕ) : Prop where
  lives i : i∈s → u i∈O.dome (D*x)
  price a : (s.filter (fun i => u i=a)).card ≤ k






end YM.SectorNext.Remainder.Affine
