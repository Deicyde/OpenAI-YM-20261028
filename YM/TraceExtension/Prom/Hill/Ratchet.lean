import YM.Next.RANK.Ratchet
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.StagePass
/-!
  Variant of YM.Next.RANK.Ratchet for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Vac.Numbers Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {c : Course C N p k} {ξ : Purse}
variable {P : (i : ℕ) → Rep G (C.side i p)} {X : AtlasData G C.S p}

variable (F : MarketGrantSky c P X R ξ)
variable (O : StampDuty C k N p d ξ.taylor (P k) ξ.era.coast.Q X)
variable {x : Points (m+1)} {e : ℝ} (H : C.Makes) (hp : C.ref d≤ k)

structure LaunchSky (C : Family G) (k : ℕ) (ξ : Purse) (w e : ℝ) : Prop where
  pane : TableReady C k w (load ξ.era) ξ.era.coast.a
  year : Spindle.year C ξ.taylor k
  length : ξ.taylor+1 ≤ (C.path.levels.params k).order
  grant : Rocket ξ.f (load ξ.era) w ξ.era.coast.a ξ.goal ξ.era.coast.Q ξ.taylor e (clim C.path.levels k) (C.path.levels.params k)
  coup : CorridorSky C.path.levels ξ.band ξ k
  numbers (n : ℕ) : n≤2 → Awakening (G:=G) ξ (clim C.path.levels k) n

include F

end YM.Next.Rank.Tapes
