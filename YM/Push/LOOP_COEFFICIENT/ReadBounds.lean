import YM.Push.LOOP_COEFFICIENT.ContinuumTrace

/-!
# Fine type-space trace comparison calculus
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Complex Matrix Lattice Laurent Bloch Filter Set
open scoped Topology ContDiff BigOperators Kronecker Matrix.Norms.L2Operator
variable {G : Gauge} {b d : Type} [Fintype b] [DecidableEq b]

namespace Reading
instance : Sub (Reading b) := ⟨fun X Y => ⟨X.plain-Y.plain,X.shift-Y.shift,X.forw-Y.forw,X.back-Y.back,X.tad-Y.tad⟩⟩

structure Sized (X : Reading b) (M r : ℝ) : Prop where
  plain : ‖X.plain‖ ≤ M/r^2
  shift : ‖X.shift‖ ≤ M/r^2
  back : ‖X.back‖ ≤ M*r
  forw : ‖X.forw‖ ≤ M*r
  tad : ‖X.tad‖ ≤ M

variable {X Y : Reading b} {M N r ε : ℝ}






end Reading








end YM.Push.Loops
