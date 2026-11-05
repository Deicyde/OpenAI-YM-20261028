import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Endow
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Leashes
import YM.TraceExtension.Prom.Port.Pleas
import YM.TraceExtension.Prom.Port.Stagecraft
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Endow for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Display.Sew Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec
     Push.SectorMeasure Next.SectorChange Paint
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {N k p i : ℕ} {w r l a : ℝ}
    (B : Binding C) (M : C.Makes) (J : ChartRatio G) (ξ : Purse)
local notation "Λ"=> C.path.levels

local notation "Υ"=> C.path.levels.params k

local notation "ℓ"=> C.path.levels.clock.factor (C.path.levels.clock.J k)
local notation "St"=> C.path.levels.clock.op i p
local notation "L"=> ξ.band
local notation "HP"=> C.path.levels.clock.hatBeta

variable (H : ShowHoursSky J B ξ k w l r)

section
-- end products
variable (hi : i<k) (hh : Station.widthSky C.path.levels ξ.band k ≤ i) {P : Rep G (C.side (i+1) p)}

variable (O : BushSky B J ξ H (N:=N) (i:=i+1) P (show i+1≤k from hi) (hh.trans (Nat.le_succ i)))
    (hp : CorridorSky C.path.levels ξ.band ξ k)
include hi hh O hp
local notation "X"=> Atlas.clim C.path.levels i
local notation "Y"=> Atlas.clim C.path.levels (i+1)
local notation "x₀"=> Atlas.clim C.path.levels k
local notation "v"=> Perch.gas ξ.era.coast
local notation "XT"=> tunnel B N i p
lemma coast_leaseSky (Q : Rep G (C.side i p)) (h₁: Q.p= Paint.inbox C i (H.oldPrices i hi.le hh)) :
    25*radiusB (retime X)+30 ≤ Q.p.B ∧ Lease (St).patch.L P.p Q.p (load ξ.era) (acres ξ X Y) (Line ξ.era ξ.goal 0 x₀) (tinder ξ x₀) (kinetics x₀) (v Y):= by
  have h':Station.widthSky C.path.levels ξ.band k≤ i+1:=hh.trans (Nat.le_succ i)
  obtain ⟨hX,hY⟩:= sizes_atSky ξ hp hh hi p
  have hx:=hp.court _ hh hi.le; have hy:=hp.court (i+1) h' hi
  have hU:P.p.B= walls Y:= O.used ▸ rfl
  have hP:= (H.flash i hh hi).clamp 0 (by decide) X hx Y hy P.p Q.p hU (h₁ ▸ rfl)
  have hθ := H.adaptive i hh hi P.p Q.p hU (h₁ ▸ rfl) hP.upper.square (O.used ▸ rfl) (h₁ ▸ rfl)
  exact ⟨hP.lamp,(hX.symm ▸ hθ)⟩
include M in
lemma holding_graphSky (hN : k ≤ N) :∃ _ : Boosted XT (tell B i) (retime X),∀ (Y':Lantern G St), Y'.hood=dressing G C.path.levels i p r →∀ D:Allocation G St (retime X) l, Coupler XT Y' J D P.beta:= by
  have h':Station.widthSky C.path.levels ξ.band k≤ i+1:=hh.trans (Nat.le_succ i)
  obtain ⟨hX,hY⟩:= sizes_atSky ξ hp hh hi p
  have hx:=hp.court _ hh hi.le; have hy:=hp.court (i+1) h' hi
  let W:=tell B i; have hw : tell B i=W:= rfl
  obtain ⟨A,-,-,hv⟩:= (H.flash i hh hi).stamp X hx _ _ St XT hX hY (C.path.levels.blocks i p).branches (H.yard i hh hi p) (show W.Funds St XT from hw ▸ ships B N i p M (hi.trans_le hN))
  let T : Boosted XT (tell B i) (retime X):= hw.symm ▸ A
  refine ⟨T,fun Y' he D=> hv _ ?_ _ (bush_posSky B J ξ hp O) D⟩
  rw [he]; unfold dressing; rw [hX]

end
end YM.PhysicalNext.InteractingRank
