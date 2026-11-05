import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Spear
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Ratchet
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Leashes
import YM.TraceExtension.Prom.Port.Pleas
import YM.TraceExtension.Prom.Port.Soft.Bonfire
import YM.TraceExtension.Prom.Port.Soft.Grows
import YM.TraceExtension.Prom.Port.Soft.Unlid
import YM.TraceExtension.Prom.Port.Stagecraft
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Spear for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    AnalyticBridge.GaussianFieldAlignment.Locations SectorNext.Vacuum
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps Display Display.Docking
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {N i p k : ℕ}
local notation "St" => C.path.levels.clock.op i p
local notation "D" => C.path.levels
local notation "x" => C.path.levels.clock.hatBeta i
local notation "y" => C.path.levels.clock.hatBeta (i+1)
structure SpearSky (B : Binding C) (g : Course C N p k) (purse : Purse)
    (H : i<k) (U z : ℝ) (P : Rep G (C.side (i+1) p)) (Q : Rep G (C.side i p)) : Prop where
  duty : Station.middleSky D purse.band k ≤ i
  canvas : roomTestSky D purse.band k p purse.horizon purse.era.coast.Q
  price : Dawn (C.path.levels.clock.op i p).patch (tell B i) (min (B.prices.α (C.path.levels.clock.J (i+1))) (B.prices.α (C.path.levels.clock.J i))) (B.prices.η (C.path.levels.clock.J (i+1))) (max (B.prices.Ω (C.path.levels.clock.J (i+1))) (B.prices.Ω (C.path.levels.clock.J i)))
      purse.era.coast.Q U z (purse.sends (Atlas.clim D k)) x (g.changeβ (i+1)) (g.changeβ i)
  fits : g.changeβ (i+1)=P.beta
  warmth : P.p.threshold=phase y
  sparks : Q.p.threshold=phase x
  walls : P.p.B=Perch.walls y
  budget : Q.p.B=Perch.walls x

lemma allocSky {J : ChartRatio G} {B : Binding C} {ξ : Purse} {f : Course C N p k} {w l r a : ℝ} {H : ShowHoursSky J B ξ k w l r} {O : LaunchSky C k ξ w a}
   (V : (i:ℕ)→ Rep G (C.side i p)) (hx : WhipSky B J ξ H O f V (Station.widthSky D ξ.band k) le_rfl)
    (hi : i<k) (hb : middleSky D ξ.band k≤ i) : ∃ u z : ℝ,SpearSky B f ξ hi u z (V (i+1)) (V i):= by
  have hc:=O.coup; have hN:= hi.trans_le f.allow; have ha:= (widerSky ..).trans hb; have he' := ha.trans (Nat.le_succ i)
  obtain ⟨hp₁,h₁⟩:=hx.outer i ha hi.le; obtain ⟨hp₂,h₂⟩:=hx.outer (i+1) he' hi
  obtain ⟨hV,hW⟩ := sizes_atSky ξ hc ha hi p
  have hz: 0 ≤ B.prices.Ω (C.path.levels.clock.J (i+1)):= minimum_price B N (i+1) hN
  have ht := hc.court i ha hi.le; have hn:=hp₂.warm.used; change (V (i+1)).p=_ at hn; have hm:=hp₁.warm.used; change (V i).p=_ at hm
  obtain ⟨W,z,h⟩:= (H.flash i ha hi).wool _ ht hz (C.path.levels.clock.op i p).patch hW hV (C.path.levels.blocks ..).branches
  refine ⟨W,z,hb,H.canvas p,?_,h₂.coupling,hn ▸ rfl,hm ▸ rfl,hn ▸ rfl,hm ▸ rfl⟩
  obtain ⟨hc,hb⟩:= bush_pricesSky B J ξ hc hp₂.warm
  rw [h₁.coupling,h₂.coupling]
  refine h _ _ ?_ ?_ (bush_pricesSky B J ξ O.coup hp₁.warm).1 ?_
  · rw [calendar_warm] at hc; unfold betaF at hc
    exact le_trans (b:=_) (div_le_div_of_nonneg_right (le_add_of_nonneg_right (Work.E04.shift_nonneg ..)) (by norm_num)) hc
  · have hℓ:= (H.flash i ha hi).melt _ ht; rw [calendar_warm, show C.S.block i=_ from hV] at hb
    change (V (i+1)).beta ≤ 2 * betaF _ _ _ at hb; unfold betaF at hb; unfold shear at hℓ;change _≤ 3*Atlas.clim _ _;linarith only [hℓ,hb]
  rw [(hx.stokes i ha hi).still,sub_self,abs_zero]
  exact add_nonneg (C.path.levels.params (i+1)).drift_ge (Work.E04.shift_nonneg ..)
end YM.PhysicalNext.InteractingRank.Soft
