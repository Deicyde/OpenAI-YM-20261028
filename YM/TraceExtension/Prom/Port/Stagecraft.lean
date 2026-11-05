import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stagecraft
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stagecraft for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
     YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory Bid Display Display.Docking Filter AnalyticBridge.LocalGaussianLaws Local RG.Supply Next.Rank.Station Tree
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} (B : Binding C) {N i k p : ℕ}
    {g : Course C N p k} (J : ChartRatio G) (ξ : Purse)


local notation "St" => C.path.levels.clock.op i p
local notation "xℓ" => C.path.levels.clock.factor (C.path.levels.clock.J (i+1))

set_option quotPrecheck false

-- call assembler
section
variable (c : Course C N p k) (V : (i : ℕ)→ Rep G (C.side i p)) (l d : ℝ)

-- no Purchase; knows next
end

section volume
-- not requiring a modified scale supposition in lower, purchases eventually for every paid schedule independently
open Asymptotics
def WaxroomSky (A : Levels G) (ξ : Purse) (k : ℕ) := ∀ i, Station.widthSky A ξ.band k ≤ i→ i<k → ∀ p,100*(1+radiusB (retime (Atlas.clim A i)))≤ (A.S.side i p).val

end volume

variable (m : C.Makes)
section access
variable (hP : CorridorSky C.path.levels ξ.band ξ k)
include hP
lemma sizes_atSky (hh : Station.widthSky C.path.levels ξ.band k ≤ i) (ht : i<k) (p : ℕ) : (C.path.levels.clock.op i p).patch.L=xℓ ∧ (C.path.levels.clock.op i p).patch.J=C.path.levels.clock.J (i+1) := by
  exact ⟨(C.path.levels.fits.sameFactor _).symm,rfl⟩

variable {l d : ℝ}
include m hP

end access
section assemblage
variable (V : (i : ℕ)→ Rep G (C.side i p)) {n : ℕ} (X : Points n) (hf : FitSky C.path.levels ξ.band k X) (hP : CorridorSky C.path.levels ξ.band ξ k)
include m hP hf
-- same Course, enough if from any purchaser of its m-moment/Dawn (see commission_epoch when keeping).

end assemblage
end YM.PhysicalNext.InteractingRank
