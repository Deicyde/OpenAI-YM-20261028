import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Algebra.MvPolynomial
import YM.Analysis.Symmetric
import YM.Cells.Tiling
import YM.RG.History

set_option warningAsError false
/-!
# Root accuracy suffices for *ordinary* products of separated translates

Together with origin-centered accuracy for each field and the ordinary centered
bounds, the actual full chessboard inequality yields comparison for any finite
arity on that grid. At this finite-torus stage the estimate does *not* require
distinct coordinate projections, only that the occupied cells are distinct!
It gives no cutoff-independent diagonal estimate with two fields occupying
the very same cell. See .
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror
open Set Filter Function MeasureTheory Cells Wilson Lattice 
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {m N p : ℕ}
variable {ι : Type*} [Fintype ι]

/-- Pre-cutoff comparison in one strict cell. Norm exponent and signs as
in `Tiling.rootTest` (price after taking the *full* replication root). Use
`Answer` (below) for positive/uniform error/budget parameters. -/
structure Gap (T : Tiling n) (β : ℝ) (F Q : Config G n → ℂ) (a e : ℝ) : Prop where
  first : Interior (T.chamber 0) F
  second : Interior (T.chamber 0) Q
  bill : T.rootTest β F ≤ a
  change : T.rootTest β (Q-F) ≤ e

namespace Gap
variable {T : Tiling n} {F Q : Config G n → ℂ} {β a e : ℝ}






end Gap






end YM.ProjectorNext.RMirror
