import YM.Next.BOUNDARY.Stage
import YM.Push.COMMON_WITNESSES.Link

/-!
# Use same W,I and pick α and fields once

We use exactly the
normalization and quotients of `Closed`.

Given the inputs, run station on
*these* witnesses.

No independent `Phase` and `Stage` hypotheses.

Go through
every ordered refinement with the calibration, the SAME compression
resolution and projection (onto ground in exact chamber), boundary witnesses
and ranks and phase null equalities, not even up-to-iso replacements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells Table Next.Extract Dash
open Spec Org OS Boundary Snap
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {b : Presentation C} {f : Order}
variable {w : Snap C} {u : Upper w}

/-- Exact remaining data requested at `RGrades` on this table, normalized per
these Climb types. Not assumptions on phase/fields. This port has no explicit
f limits; if producers select further orders to get it, must keep the same
T, I etc. (use `upon`, one application system). -/
def Grades (H : Risen u b f) (W : MaxwellData C) (I : IR (C:=C) u.T) :=
    Climb.Pre H.base.kernel u.V I.J I.p I.Y ∧ Climb.ActLaw u.V W.T I.J H.base.kernel.spin W.hT.spin

/-- Final data not depending definitionally on order; `Playing` (with order)
certifies them. Sector including stress from Station. Don't introduce
extraction parameters free of the Family. -/
structure Cast (u : Upper w) (W : MaxwellData C) (I : IR (C:=C) u.T) where
  rate : ℝ
  map_ : ∀ d, _root_.YM.Spin.change u.T d
  stress : u.T.Stress
  spin : Spins u.T
  α : Selection u.T
  unselected : Contour u.T
  selected : Contour u.T
  model : Wightman u.T

variable {Y : Guests u.T} {W : MaxwellData C} {I : IR (C:=C) u.T}

abbrev Cast.sector (Z : Cast u W I) : Algebra u.T := ⟨u.V, mill W I Z.rate Z.map_, Z.stress⟩

/-- One record that will give `Final`, with additional actual boundary
compatibility on BOTH Contours. In particular keeping: Materializes tells
what the null spaces of EVERY character on this resolution are; boundaries
have on this data the lifts/spins/& attachments of Compatible.
-/
structure Playing (u : Upper w) (b : Presentation C) (Y : Guests u.T)
    (W : MaxwellData C) (I : IR (C:=C) u.T) (Z : Cast u W I) (f : Order) : Prop where
  trajectory : Calibrated C
  estimates : Hosted u b Y f
  uv : UV C f u.T u.V W I
  costs : Tab u.T u.V W I uv Z.rate Z.map_ Z.stress
  letters : Z.spin.Descends Z.sector.turns uv.basis.kernel.spin
  material : Materializes Z.sector Z.α uv.basis.kernel.spin
  fields : Relativistic Z.sector Z.α Z.unselected Z.selected Z.model uv.basis.kernel.spin
  letter : Z.model.spin=Z.spin
  compatible : Next.BOUNDARY.Compatible u.T Z.α.unselected Z.sector Z.spin uv.basis.kernel.spin Z.unselected
  retains : Next.BOUNDARY.Compatible u.T Z.α.slabs Z.sector Z.spin uv.basis.kernel.spin Z.selected

namespace Playing
variable {Z : Cast u W I} (H : Playing u b Y W I Z f)
include H






end Playing


end YM.Push.Common
