import YM.Extra.FREE_DETECTOR_ALGEBRA.Columns
import YM.Extra.FREE_DETECTOR_ALGEBRA.Conduit

set_option warningAsError false

/-! One bounded family with actual exterior labels and locations. Every
input read at any higher cutoff. Moreover for each cap, finitely MANY
placements (generic) suffice with this FIXED family. Uses same_rows even if
basis contains unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels SphereTest Residue OPE Ward Climb MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder Matrix ENNReal

variable {G : Gauge} (F : Frames G) {d e m n j : ℕ} {x : Points n}
local notation "W" => Table.Field (freeTable F)
local notation "T" => freeTable F
local notation "γ" => writes F

abbrev pack (i : (F.level d).Index) : W d := sourceAt F d ((F.level d).basis i)

-- readers with bounded spectators only
structure Listener (F : Frames G) (d : ℕ) where
  n : ℕ
  x : Points (n+1)
  hears : x ∈ generic (n+1)
  ext : Fin n→ (F.level d).Index




-- multilinearity in existing finite input frame






-- D* truly independent of output e.

end YM.Extra.FD
