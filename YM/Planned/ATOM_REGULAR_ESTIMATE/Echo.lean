import YM.Planned.ATOM_REGULAR_ESTIMATE.Sampled
import YM.Planned.ATOM_REGULAR_ESTIMATE.Vest



/-!
Small-parameter transport on an actual uniformly produced stationary graph.
Panel parameters measured in increment budget, *not log directions in unit
field scale*. Fold transport into `Judged` using a remaining linear
valuation estimate and log-frame displacement bounds relative to station
for any integral using it. In particular if constructing rolling estimates
on localized kernel terms via those stationary paths there is no need to
assume this nonlinear sensitivity too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Foliage
open Function Set Metric Filter RG Wilson Precision Lattice Tree Pressure Bid Push Uniform
open WardBin.Lies Short Sample
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {n m : Side} {G : Gauge} {k K i j l d : ℕ}

section Remainder
variable {E F Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {C r : ℝ} {U : E → F} {V : Z → E} {x : Z}

/-- All at the chosen point of the parameter panel. -/
structure Clips (V : Z → E) (x : Z) (n : ℕ) (r : ℝ) : Prop where
  germ : ContDiffAt ℝ n V x
  size : ∀ l, l≤n → ‖iteratedFDeriv ℝ l V x‖ ≤ r


def ray (U : E → F) := fderiv ℝ U 0



end Remainder

end YM.Planned.AtomRegular.Foliage
