import YM.Next.RANK.ShapeS
import YM.TraceExtension.Prom.Hill.Cadence
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.Next.RANK.ShapeS for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points m} {hk : i≤k} {hi : middleSky C.path.levels b k ≤ i}
variable {c : Course C N p k}
variable {ξ : Purse}

structure CorridorSky (A : Levels G) (s : ℝ) (p : Purse) (k : ℕ) : Prop where
  heft : AllowedSky A s k
  races : Racer p (clim A k) (k-middleSky A s k)
  spend : Faring p (clim A k)
  court i : Station.widthSky A s k ≤ i → i≤k → clim A i∈ Set.Icc (clim A k/2) (clim A k)

variable (X : AtlasData G C.S p) (F : Lead G C.S p)
section
variable {P : Rep G (C.side k p)} (W : StampDuty C k N p d ξ.taylor P ξ.era.coast.Q X)
variable (Y : CorridorSky C.path.levels b ξ k) (v : Fin m→ C.label d)
variable (O : KFlux (C:=C) k (middleSky C.path.levels b k) X ξ F)
variable (Z : ∀ i, coin (W.W (v i))≤ ξ.principal (clim C.path.levels k))
include Y

include Z O

variable (i : ℕ) {Q : Rep G (C.side i p)} (R : ReadyShSky (A:=C.path.levels) b X ξ.horizon ξ.era.coast.Q k F) (x : Points m)
variable (hk : i≤k) (h : middleSky C.path.levels b k ≤ i) (c : Course C N p k)

end
end YM.Next.Rank.Tapes
