import YM.Next.RANK.StagePass
import YM.TraceExtension.Prom.Hill.Cadence
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.Next.RANK.StagePass for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points m}
variable {c : Course C N p k}
variable {ξ : Purse}
variable {P : (i : ℕ) → Rep G (C.side i p)} {X : AtlasData G C.S p}

-- Mall. A step affidavit Cγ. property Path - sparse hierarchy specialized to window after k producers.
structure MarketGrantSky (c : Course C N p k) (P : (i : ℕ) → Rep G (C.side i p)) (X : AtlasData G C.S p) (R : Lead G C.S p)
    (ξ : Purse) : Prop where
  fund i : Station.widthSky C.path.levels ξ.band k ≤ i → ∀ h : i ≤ k, Candle c i (P i) (h.trans c.allow)
  paths : ReadyShSky (A:=C.path.levels) ξ.band X ξ.horizon ξ.era.coast.Q k R
  probes : KFlux (C:=C) k (middleSky C.path.levels ξ.band k) X ξ R
  invariant : invariantAt (C:=C) k (wood C.path.levels k) p X
  stencil : Hail C k p ξ.taylor X

namespace MarketGrant
variable (F : MarketGrantSky c P X R ξ)
include F

end MarketGrant

variable (F : MarketGrantSky c P X R ξ)

variable (O : StampDuty C k N p d ξ.taylor (P k) ξ.era.coast.Q X)
variable (v : Fin m→ C.label d)
variable (H : CorridorSky C.path.levels ξ.band ξ k) (he : FitSky C.path.levels ξ.band k x)
variable (hn : m≤2) (Hv : Crew c P R ξ x)

-- passage at fixed F, x,v; W forecast includes all R.Inc budgets already accumulated

include H he hn Hv F

end YM.Next.Rank.Tapes
