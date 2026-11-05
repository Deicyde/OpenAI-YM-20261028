import YM.Next.WARD_BIN.Rack

/-!
# Offsets: same step console, calibrated *there*

alternatives for reference and hierarchy ancestry.

Establish Woke on any matched signed entry, incl at
intermediate k.

No angular action demanded or proclaimed on these alternatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Offsets
open Function Set Filter Topology MeasureTheory Wilson Lattice RG Gas Source Bid Work.G08
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {l m k r' t N p d i : ℕ} {v w r b c : ℝ} {W : Worth}
    {T : Console C.path p (brim C d)} {A : Chart C d} {X : Page C d N p} {S : Finset Cover}

-- These section gates obtainable for *all* large N, all offsets of C
structure OffsetPrice (A : Chart C d) (o : Site (C.side N p)) : Prop where
  pose : FitsIn A.art.cover (C.side N p)
  owes : stipend C.params (C.localSection d) (face C N p) A.art.cover o (A.ush N)
  silver : inkage (face C N p) (footprint A.art.cover o) d (cash C N) (κ C.path N)
  flag : let Y:=footprint A.art.cover o; let P:=face C N p
         P.mass Y (A.ush N)*(P.threshold⁻¹^d*(Real.exp (Y.card*cash C N)-1)) ≤ κ C.path N*rentAt C N
  expY : coverNumber (face C N p).B (footprint A.art.cover o) ≤ 1



variable (D : Pad (roof C N p).activities (face C N p))

-- Chosen Console format; for offset p.N from given genealogy. All roots included.
structure Way (A : Chart C d) (L : Console C.path p (brim C d)) (W : Worth) (N l i : ℕ) : Prop where
  up : l ≤ N
  purchases : L.Purchases l N N W (C.localSection d) C.params
  at_desk : OffsetPrice A (L.centers N)
  ink : L.rods N i=footprint A.art.cover (L.centers N)
  holds j : L.centers N ∈ L.rods N j















end YM.WardBin.Offsets
