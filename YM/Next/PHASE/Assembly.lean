import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Bid.Market
import YM.Next.PHASE.Seats
import YM.Pressure.Seeds
import YM.Work.B01
import YM.Work.B02
import YM.Work.B03
import YM.Work.B04
import YM.Work.B05
import YM.Work.B06
import YM.Work.B07
import YM.Work.B08
import YM.Work.B09
import YM.Work.B10
import YM.Work.B11
import YM.Work.B12
import YM.Work.B13
import YM.Work.B14
import YM.Work.B15
import YM.Work.B16
import YM.Work.B17
import YM.Work.B18




/-!
# A materializing phase from RSeed, locals and the grid port

All on the very same Seed. No boundary premise to get the phase,
no supposition that selecting a chamber with unique heat ground state
will preserve rank. Reuse the existing assembly proofs once the `Seats`
prerequisite is discharged.

The physics/grid/rotation inputs remain conditional. In particular B05
is a consumer that needs not only Seed but `Grill C F`; the analysis
on ground reflection from ordinary-real cutoff approximation has not been licensed by
Seed alone here. In the planned route this argument will come from the
RGrill obligation (`UV.tables`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Phase
open Spec Org MeasureTheory OS Extraction Filter
open scoped Topology

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}



/-- RSpan through RStates arcs, including norm derivatives and all-copy in
 `Spread.Laws`, and `Stall` including reflection (ordinary theta), all-index
 services at `Vendor` (in particular its `bags` component, using B02 **again**
 with input from B13), and all `Trials.Valid` ⇒ Funds. Exact type consumed
 at `Org.Continuum.vacuum`. -/
theorem vacuum (s : Seed C f S) (X : Spec.Algebra S) (h : Grill C f) : Org.Phase.Loom s X h :=
  Bid.Looms seats Work.B01.answer Work.B02.answer Work.B03.answer Work.B04.answer Work.B05.answer
    Work.B06.answer Work.B07.answer Work.B08.answer Work.B09.answer Work.B10.answer Work.B11.answer
    Work.B12.answer Work.B13.answer Work.B14.answer Work.B15.answer Work.B16.answer Work.B17.answer
    Work.B18.answer h s X

/-- RFullRes/RPhase. `cleanse` uses this Loom on actual `Locals` (proper
 rotation inputs etc.), producing compression resolution, hierarchy for
 **every** character, selecting after the AE unique-heat argument at the same
 resolution, and closing the null-equality obligation using the *actual*
 `s.corrected` trials' funds. Thus the `normalized`, `field_union` and
 `still_separated` transfers apply to this selection with no further
 detection/normalization assumptions. -/
theorem material (s : Seed C f S) (X : Spec.Algebra S) (h : Grill C f) (ht : Locals X s.kernel.spin) :
    ∃ P : Selection S, Materializes (C:=C) X P s.kernel.spin :=
  (vacuum s X h).cleanse ht

/-- Even the individual calibrated probe row limits used for rank are
 available on this resolution, for any character (not just `P.atPoint`).
 Not claiming a phase is itself a cutoff limit. Use with `s.corrected d`
 (which supplies existing valid widths at each d). -/
theorem rows (s : Seed C f S) (X : Spec.Algebra S) (h : Grill C f) (P : Selection S)
    (ht : Materializes (C:=C) X P s.kernel.spin)
    (d) (W : Cells.Columns C S d) (T : W.Trials) (K : Cells.Columns.Trials.Valid f T)
    (i : P.space.X) (j : Fin W.amount) (c : Fin (W.dim+1)) :
    Tendsto (fun k => Retain.probe' (D:=P.ensemble i) T k j ((P.ensemble i).project d (T.later k c))) atTop
      (𝓝 ((W.row j).tests (Cells.standard C) W.basis (W.basis c))) := by
  have hs := (vacuum s X h).sale ht.transport P.room P.unselected ht.phase.lengths
  exact Retain.result T K P.unselected P.space (hs.funds d W T K) ht.phase.decomposition (ht.phase.chosen i)
    (ht.phase.states i).laws.toSymmetric j c


end YM.Next.Phase
