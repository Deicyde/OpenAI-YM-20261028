import YM.Extra.MULTISOURCE_TRAJECTORIES.Geometry
import YM.Extra.MULTISOURCE_TRAJECTORIES.Trials
/-!
# `Lease.rents` sufficient criterion with actual mixed transports

Arbitrary link tilings with the stated side and relative margins; positions
needn't be central/aligned with a blocking grid. Price tests at a stop are
hard physical inequalities on the very cylinders and copies and unmarked
vacuum; no such price is obtained from matching a column in isolation here.
These are optional inputs for discrepancy problems, not used to prove Circle.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open RG Wilson Lattice Overlay Marker Mix Stock Extraction Cells Function Filter MeasureTheory Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {N p j k : ℕ}
namespace Cylinder
variable (F : Cylinder C) (T : Tiling (C.side N p)) (x : Site (C.side N p))

def copies (d : ℕ) : Insertions C.path T.Cell N p where
  load _ := d
  field i W := if T.hand i then star (F.field N p x (pullM (T.omega i) (T.translateBy i) W)) else
    F.field N p x (pullM (T.omega i) (T.translateBy i) W)
  smooth i := by
    have he := (F.smooth N p x).comp (pullM_smooth (G:=G) (T.omega i) (T.translateBy i))
    split
    · exact (starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp he
    exact he

def native := F.stencil.image (fun v => wrap (C.side N p) v + x)

def marked (i : T.Cell) := (F.native x).image (T.copyMap i)










end Cylinder








namespace Cylinder
variable (F : Cylinder C) (T : Tiling (C.side N p)) (x : Site (C.side N p)) (d : ℕ)

def booth (W : Windows (C.side j p)) := (F.copies T x d).fragments (Stock.census _) W (fun i => ancestor C.path p N j (T.copyMap i x))
    (fun i => (F.marked T x i).image (ancestor C.path p N j))











end Cylinder
end YM.Extra.Trajectories
