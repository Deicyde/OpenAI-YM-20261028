import YM.Next.RANK.Promises
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.Next.RANK.Promises for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Wall
open Function Set Lattice Wilson RG Normal Perch Prayer  Atlas Station CellsInt Configuration Glimmer Filter Beamer Maxwell
open scoped Topology BigOperators Classical

variable {G : Gauge} (A : Levels G) {k n d : ℕ}

def stretchSky (b : ℝ) (k : ℕ) := A.S.a (middleSky A b k)/ A.S.a k

def VantageSky (d k p n D : ℕ) (b : ℝ) (F : AtlasData G A.S p) :=
    Model A d k p F ∧ Fell F (beforeSky A b k) d (stretchSky A b k) (fraction n D (clim A k))

end YM.Next.Rank.Wall
