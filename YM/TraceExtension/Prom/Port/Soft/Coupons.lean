import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Coupons
import YM.TraceExtension.Prom.Hill.Cadence
import YM.TraceExtension.Prom.Hill.Ratchet
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.StagePass
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Epoch
import YM.TraceExtension.Prom.Port.Leashes
import YM.TraceExtension.Prom.Port.Pleas
import YM.TraceExtension.Prom.Port.Soft.Bonfire
import YM.TraceExtension.Prom.Port.Soft.Grows
import YM.TraceExtension.Prom.Port.Soft.Postsale
import YM.TraceExtension.Prom.Port.Stagecraft
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Coupons for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph Atlas Value Flux Marker Rise Normal Ribbon Spindle Glyph Exponential Camp Cells Edition Relation EntryWord Alarm Corona
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {N i p k : ℕ} {w r l a : ℝ}
local notation "St" => C.path.levels.clock.op i p
local notation "D" => C.path.levels
local notation "x" => C.path.levels.clock.hatBeta i

section
-- terminal family comparison with *end receipts* to use independently of heating

structure NylonSky (c : Course C N p k) (P : (i : ℕ)→ Rep G (C.side i p)) (X : AtlasData G C.S p) (R : Lead G C.S p) (ξ : Purse):Prop where
  use_ i (h : Station.widthSky C.path.levels ξ.band k ≤ i) (H : i ≤ k): Novice c i (P i) (H.trans c.allow)
  backing : ∃ (T : (i:ℕ)→ Rep G (C.side i p)) (c' : Course C N p k), MarketGrantSky c' T X R ξ ∧ T k=P k
namespace NylonSky
variable {P : (i:ℕ)→ Rep G (C.side i p)} {c : Course C N p k} {X R ξ} (F : NylonSky c P X R ξ)
include F
lemma fixture (H : middleSky C.path.levels ξ.band k ≤ i) (h : i≤ k) : Novice c i (P i) (h.trans c.allow):= F.use_ i ((Station.widerSky ..).trans H) h
lemma paths : ReadyShSky (A:=C.path.levels) ξ.band X ξ.horizon ξ.era.coast.Q k R:= F.backing.choose_spec.choose_spec.1.paths
lemma probes : KFlux (C:=C) k (middleSky C.path.levels ξ.band k) X ξ R:= F.backing.choose_spec.choose_spec.1.probes
lemma invariant : invariantAt (C:=C) k (wood C.path.levels k) p X:= F.backing.choose_spec.choose_spec.1.invariant
lemma stencil : Hail C k p ξ.taylor X := F.backing.choose_spec.choose_spec.1.stencil
end NylonSky
end
section construct
variable (B : Binding C) (J : ChartRatio G) (F : Course C N p k) (ξ : Purse) (M : C.Makes)
    (H : ShowHoursSky J B ξ k w l r) (Z : VentsSky B ξ J l r k) (O : LaunchSky C k ξ w a)
    (V : (i:ℕ)→ Rep G (C.side i p)) (A : WhipSky B J ξ H O F V (Station.widthSky C.path.levels ξ.band k) le_rfl)
include Z O A M
lemma embroideredSky (hb : 0≤ ξ.band) : NylonSky F V (stamp D N p) (short B N p) ξ:= by
  have hx i (hi : middleSky D ξ.band k ≤ i) (hp : i<k):= (H.flash i ((widerSky ..).trans hi) hp).monitor; let L:=Station.widthSky C.path.levels ξ.band k; let G':= (C.path.levels.params k)
  constructor
  · intro i hp hv; by_cases h:i=k
    · subst i
      obtain ⟨⟨T,σ,g,h,h₁,h₂,hu,ht⟩,W,Y⟩:= Paint.lights C F.allow F M O.pane _ A.stops
      exact ⟨⟨T,_,_,_,_,_,hu,cloth _ ht⟩,W,Y⟩
    have hi:i<k:= lt_of_le_of_ne hv h
    obtain ⟨P,U⟩:= A.outer i hp hv
    have he := P.pets
    have hk:(V i).p= _:= P.warm.used
    refine ⟨⟨U,?_⟩,hk ▸ rfl,hk ▸ rfl⟩
    obtain ⟨g,X,e,W,z,hg,h⟩:= groomSky B J ξ O.coup P.warm
    obtain ⟨b,-,hv,hl⟩:= elongationSky B J ξ Z O.coup hi hp (p:=p)
    refine ⟨_,g,_,_,_,⟨hg.same,hg.cap,hg.assigned,hg.positive,hg.entrance,hg.max_threshold,hv.rate _ hl, le_rfl⟩,he⟩
  obtain ⟨Y,h,hV,T⟩:= earn_epochSky B ξ M O F.allow hx H.arrival H.oldPrices (H.canvas p)
  let R:= Function.update Y k (V k)
  have hR: R k=V k:= Function.update_self ..
  refine ⟨R,keeping M p N k F.allow,ordersSky B ξ hx H.arrival O.coup (H.canvas p) _ _ ?_,hR⟩
  intro i hp he; by_cases Hi:i=k
  · subst i; rw [hR]; exact Paint.lights C F.allow _ M O.pane _ A.stops
  rw [show R i=Y i from Function.update_of_ne Hi ..]; exact hV.fund _ hp he
end construct
-- Chorus on these Novices, same Pleases

end YM.PhysicalNext.InteractingRank.Soft
