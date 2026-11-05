import YM.SectorNext.RECONNECTED_LOCALITY.Radiance


set_option warningAsError false

/-!
# Weather toll in four dimensions

Use true periods and actual output positions $d_L$ , not an abstract
growth assumption on the random geometry. Radar also allowed on fine parent
coords; charge all residues and all colors per physical location (linear, not
row/column-product loss). Curve / cost not assumed summable with L uniform.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Ice
open Finset Matrix Lattice
open scoped BigOperators

variable {I κ : Type*} {c f : Side}

def land (p : I→Site c) : Radar I := {
  d i j := separation (p i) (p j)
  down _ _ := Nat.cast_nonneg _
  same i := by simp
  back i j := by rw [separation_comm]
  chain i j k := by exact_mod_cast separation_triangle (p i) (p j) (p k) }














end YM.SectorNext.Reconnect.Ice
