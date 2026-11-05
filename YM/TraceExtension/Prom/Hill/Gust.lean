import YM.Next.RANK.Gust
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Memorandum
/-!
  Variant of YM.Next.RANK.Gust for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Marker Value Perch Vac.Numbers Alarm Spindle Station Cells Glyph Atlas
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {F : Family G} {N k i v d p : ℕ} {b : ℝ} {x : Points v}

-- conjugation selector

-- $μ$ axis consistency for *any* rolled price at the course

-- actual bill, all fields and markers. T width cell set depends ONLY on p.

variable (C : Family G) (b : ℝ) (x : Points v) (hN : k ≤ N) (p : ℕ)


abbrev ListensSky := (Ship.yardSky C b hN p).Cell × Fin v

def fpSky (m : ListensSky C b (v:=v) hN p) := (Ship.yardSky C b hN p).hand m.1
def handSky (m : ListensSky C b (v:=v) hN p) := (Ship.yardSky C b hN p).omega m.1

def seatsSky : ListensSky C b (v:=v) hN p→ Site (C.side k p) := Peak.readersSky (C:=C) x hN hN

def pullerSky (i : ListensSky C b (v:=v) hN p) := pull (K:=G.El) (handSky C b hN p i) (seatsSky C b x hN p i)

end YM.Next.Rank.Edition
