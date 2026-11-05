import YM.Next.RANK.Joints
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.Next.RANK.Joints for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Cells Station Ac Alarm Thirst Corona Value Finset MeasureTheory Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {B : Side}
variable {S : Schedule} {C : Family G} {A : Levels G} {i k l j m p q D N d n : ℕ}
variable (x : Points n) (s : ℝ)

abbrev CellPSky (C : Family G) (k : ℕ) (s : ℝ) (p : ℕ) := Site (C.side (Station.widthSky C.path.levels s k) p)

-- orphan singleton always present. hMask center inherited exactly before κ formation.

def watchesSky (C : Family G) (s : ℝ) (p) (h : k≤N) (i) (Q : middleSky C.path.levels s k ≤ i) (a : CellPSky C k s p) :=
    pull (K:=G.El) ((Ship.yardSky C s h p).omega a) (spreadCSky C s p ((Station.widerSky C.path.levels s k).trans Q) a)

def glorySky (p : ℕ) (hN : k≤N) (hk : i≤k) (hi : middleSky C.path.levels s k ≤ i) (H : CellPSky C k s p) (j : pennant n) (c : ℝ) (P : poly (Chamber G C.S i p)) :=
  let T:= Ship.yardSky C s hN p; let R:=core C.path.levels x s p hk (headMark j); let A:= watchesSky C s p hN i hi H
  Edition.dot (T.hand H) ∘ caseW P R c ∘ A

end YM.Next.Rank.Tapes
