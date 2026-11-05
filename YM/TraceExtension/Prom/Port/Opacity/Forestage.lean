import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Forestage
import YM.TraceExtension.Prom.Port.Soft.Postsale
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Leashes
import YM.TraceExtension.Prom.Port.Pleas
import YM.TraceExtension.Prom.Port.Stagecraft
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Forestage for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis
     Pump Display.Sew Vale PhysicalGuard7f546.Curved Tree Push.SectorMeasure Oriented
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {N k p i : ℕ} {w r l a : ℝ}
    (B : Binding C) (M : C.Makes) (J : ChartRatio G) (ξ : Purse)
local notation "Λ"=> C.path.levels

local notation "Υ"=> C.path.levels.params k
local notation "b"=> C.path.levels.clock.J k
local notation "ℓ"=> C.path.levels.clock.factor (C.path.levels.clock.J k)
local notation "St"=> C.path.levels.clock.op i p
local notation "H₀"=> ξ.band

local notation "t"=> tunnel B N i p
local notation "s"=> Atlas.clim C.path.levels k
local notation "X"=> Atlas.clim C.path.levels i
local notation "y"=> Atlas.clim C.path.levels (i+1)
local notation "K0"=> Station.widthSky C.path.levels ξ.band k
-- Inputs
variable (H : ShowHoursSky J B ξ k w l r) (Z : Soft.VentsSky B ξ J l r k) (O : CorridorSky C.path.levels ξ.band ξ k) (hN : k ≤ N)
    {P : Rep G (C.side (i+1) p)} (hi : i<k)(hl : Station.widthSky C.path.levels ξ.band k ≤ i) (hP : BushSky B J ξ (N:=N) H P hi (hl.trans (Nat.le_succ i)))
-- position frame independent of P amplitude; actual `Kept` ties projections.
def tabloidSky (hc : i<k) (hz : Station.widthSky C.path.levels ξ.band k≤ i) (P : Rep G (C.side (i+1) p)): Dyed G St := ⟨P,t,Chi.canonical,J,dressing G C.path.levels i p r, Paint.inbox C i (H.oldPrices i hc.le hz),
    (Orchard.canopy St).table 0, Classical.choice (show Nonempty (St).Choices from by obtain ⟨v,h⟩:= exists_alive (C.path.levels.blocks i p).branches (1:Config G (C.side (i+1) p)); exact ⟨v⟩)⟩

local notation "Ψ"=> tabloidSky B J ξ H hi hl P (N:=N)
include hN M hP Z O hl in
lemma fitPostSky : Seeks (Ψ) (tell B i) r X:=by
  obtain ⟨hL,hJ⟩:= sizes_atSky ξ O hl hi p
  have he : i+1≤k := hi; have hf : K0≤ i+1:=hl.trans (Nat.le_succ i); let j:=C.path.levels.clock.J k
  obtain ⟨Θ,-,-,hF⟩:= Z.great i hl hi
  have hT := hF.onRoad.timing X (O.court i hl hi.le); obtain ⟨h1,h2⟩:= hT
  obtain ⟨hq,hz⟩:= h2 Λ i p hJ hL (C.path.levels.blocks ..).branches rfl; let Y:= Ψ
  have hx:y=betaF G X (St).patch.L:= calendar_warm ..
  have ht:P.p.B=Perch.walls y:= hP.used ▸ rfl
  have hv:(Y).bp.B=Perch.walls X:= rfl
  have hp:Y.bp.threshold=temp (retime X):=h1.symm
  have h' : P.p.threshold=Paint.phase y := hP.used ▸ rfl
  have hs: i<N:= hi.trans_le hN; have hB:= ((H.flash i hl hi).clamp 0 (by decide) _ (O.court _ hl hi.le) _ (O.court (i+1) hf he) P.p Y.bp ht hv).upper.square
  have hm:= B.pays.stack N i p hs
  have hg:= bush_pricesSky B J ξ O hP
  refine ⟨ships B N i p M hs,rfl,hP.exactTree.symm,hP.exactClip.symm,hp,H.yard i hl hi p,B.sized ..,
    ⟨B.world.H N (i+1),B.world.H N i,B.paths N _ hs _,B.paths N _ hs.le _,B.pays.crossings N i p hs,hm,⟨_,_,_,_,B.pays.all N _ hs _,B.pays.all N _ hs.le _⟩,B.sworn _ _ hs _,B.sworn _ _ hs.le _⟩,
    ⟨_,_,_,hP.rated,by rw [hL]; exact hq,hz⟩,hP.used ▸ rfl,⟨hv,hB⟩,?_,h'.trans (congr_arg _ hx)⟩
  rw [←hx]; exact hg

-- output record. Branch-specific scalar can use THIS serialization. Need equality on outputs ALL fields in Resin.

-- Ticket is chosen AFTER caller P and H. Does not use guessed Rep Q.

end YM.PhysicalNext.InteractingRank
