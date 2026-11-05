import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Next.MULTISOURCE.Curves
import YM.Push.GRID_APPROXIMATION.Polynomial

set_option warningAsError false

/-!
# Independent sufficient one-step producer: scalar response on sparse cones

Even the local red `UnitTest` (already before trying to sum/stop
censuses) has substantial producer prerequisites expected from same Lens
as unmarked and one-source. Here's an additional adapter to that gate,
with no assertions about lifting to the hypotheses of E LG step or their
soundness. Uses an unmarked ordinary scalar stability estimate, not assuming
anything on the squarefree derivatives. Radius domain not any positive
polydisc after reading the whole list: only need estimates sitting on the
*relevant* compatible cones of input directions (disjoint, anchored)
and on some perhaps *much smaller* unrestricted inputs. Can use either
the stronger full discs (e.g. an `allot` cone as in Multi.Curves, funding
further service in that library) or just this sparse service. Still need
shelved support (even here only the anchors suffice). And must keep the very
same reservoirs on those discs; each axis alone does not imply it.

Our signed use needs possibly other exact outputs in single-root responses
than Stable calls! Must purchase this estimate on the actual one-C system.

Proof inspired by Multi.Desk.pawns & .serialize for RMixed (also imports
their component lemmas). Here `pawns` itself doesn't apply (domains and
required assumptions don't match). Get the appropriate prices from
Evaluations and sleep laws. Numerical leg only needs large-radius discs;
representation leg may be tested at the small radius, but on the *same*
T and its authentic support labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Stepwise
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi
open MvPolynomial Finset Multi.Desk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {I : Type} [Fintype I] [DecidableEq I]
variable {n : Side} {G : Gauge} {P : Rep G n}

def candle (S : Finset I) (b : ℝ) := fun i:I => if i∈S then b⁻¹ else 0

 

variable (T : Reservoir P I) {κ b : ℝ} (S : Finset I)



-- adapt Ledger.pawns to domain

end YM.AnalyticNext.GridStop.Stepwise
