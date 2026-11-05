import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import YM.Analysis.SmoothJets
import YM.Pressure.Rows

set_option warningAsError false

/-!
# Taylor combinatorics for position estimates, pulse denominators.
Use real-list derivatives to record the exact mixed directional valuations
including a single rough input. Not a commutativity assumption on the
Lie field.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Orchard
open Lattice RG Laurent Exterior Wilson Precision Tensor Analysis
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius

section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F T : X → Y}

/-- conventional iterated D (first direction acts last in time, mixed
partial at smooth functions). -/
def spray (F : X → Y) : List X → X → Y
| [] => F
| a::l => Analysis.D a (spray F l)









variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]


end



section
variable {X Y Z T : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup T] [NormedSpace ℝ T]




end
end YM.Progress.ClassicalKin.Orchard
