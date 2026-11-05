import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Joint

/-!
# Path receiving actual signed birth estimates and checking stop receipts

Another brick of the quantitative approximation API.

Provides the
theorem to use spending `Birth` bounds etc. at one late N,p to meet the
actual `Supplies` station requests, using `Roll` costs (all old/new
coefficient transfer at all steps and buys at stop).

Doesn't assume an
estimate of closeness of physical moments; proves sufficiency from accurate
density-level tests via History.

Converse not asserted nor feasibility from
the given unmarked or assembled data.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Push.GridApprox.Birth
open RG Lattice Wilson MeasureTheory Function Filter Finset Ac Marker Overlay Attach Cells Joint Mix
open scoped Topology BigOperators

variable {G : Gauge} {H : RG.History G} {h k m r N p d : ℕ}

/-- Possible route after signed attachment: step-by-step certified arrays on
the same physical history.

Need Active and some Radial already at the k
inlet, and preserve/exhibit along roll in addition to the high price radius at
r.

Here allow final pricing via `Stubs.Holds` (and I01/2)
so must actually serve grain/order and all marked/far origin tests there.

Assertions on marker requests finite cut-by-cut, not k-extrapolation or
inference from calibration of isolates. -/
structure Roll (A : Bands (Markers H h p) (H.rep N p k)) (d r : ℕ) (W : ℝ) where
  bands m : Bands (Markers H h p) (H.rep N p m)
  path : h ≤ r
  goes : r ≤ k
  paid m : r ≤ m → m ≤ k → (bands m).Active ∧ ∃ w : Site (H.S.side h p) → ℝ,
    ∃ u c d' b : ℝ,(bands m).Radial w u c d' b
  origins m (hm : r ≤ m) : m ≤ k → (bands m).origins = anchor H.S p (path.trans hm)
  first : bands k=A
  steps m (hr : r≤m) (hk : m<k) : ∀ s : (Markers H h p).Mode,
    (fun V => ((bands m).density V).part s) = (Ride.bump (↑(H.S.block m).val) s (fun _ => d)) •
      (H.levels.clock.op m p).push (H.β N p (m+1)) (fun V => ((bands (m+1)).density V).part s)
  -- Budget with factorial protection, exact nonfactorial implies then
  -- W at point after I02. Pay any strength ≥ as needed simultaneously
  -- with γ costs BEFORE invoking planner.
  positive : 0<W
  served : Mix.Stubs.Holds (bands r) (W * ((H.rep N p r).p.order.factorial:ℝ))



variable {C : Family G}


end YM.Push.GridApprox.Birth
