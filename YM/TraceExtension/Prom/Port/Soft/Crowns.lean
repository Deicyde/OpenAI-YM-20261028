import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Crowns
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Flux.Conductor
import YM.TraceExtension.Prom.Hill.Flux.Grader
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Ratchet
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
import YM.TraceExtension.Prom.Port.Brocade
import YM.TraceExtension.Prom.Port.Emulation
import YM.TraceExtension.Prom.Port.Pleas
import YM.TraceExtension.Prom.Port.Soft.Grows
import YM.TraceExtension.Prom.Port.Soft.Spear
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Crowns for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Display Display.Docking
section daylight
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
     YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory Bid
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {i k N p n : ℕ} {ξ : Purse}
    {g : Course C N p k} {B : Binding C} {ht : i<k} {o z : ℝ}
    {P : Rep G (C.S.side (i+1) p)} {R : Rep G (C.S.side i p)}
    (φ : SpearSky B g ξ ht o z P R) (m : C.Makes)

local notation "XL" => Atlas.clim C.path.levels i
local notation "XF" => Atlas.clim C.path.levels (i+1)
local notation "τ" => Atlas.clim C.path.levels k
local notation "BT"=> tunnel B N i p
local notation "St" => C.path.levels.clock.op i p
local notation "E" => load ξ.era
local notation "IX" => Line ξ.era ξ.goal 0 τ
local notation "K" => kinetics τ
local notation "GAS" => Perch.gas ξ.era.coast
local notation "M" => (GAS XL^2)⁻¹
section
include φ m
lemma daypay_Sky (Y : Lantern G St) (s : Site (C.side (i+1) p)) (U : Config G (C.side i p)) (A : Stores St) (hp : Positioned (retime XL) A U) (j : Streak Y.park) :
    (viewer BT A (retime XL) j.wood j.tag U).real (Prod.snd ⁻¹' away (parasol s (ξ.era.coast.Q*walls XF)) (haze G XL P.beta (C.path.levels.clock.op i p).patch.L/2)) ≤ XL^(-(1:ℝ)):= by
  rw [calendar_warm,← φ.fits]
  let h:= φ.price; let J:= ships B N i p m (lt_of_lt_of_le ht g.allow)
  refine (shade_auth A j.wood XL Y.χ s ξ.era.coast.Q U BT j.tag h.steady.visible h.steady.sparks h.strong.cash h.heat le_rfl (h.strong.ribbon St BT rfl J (B.sized i p) ?_ _ _ j.tag U hp _)).2
  exact hot_fitsSky ξ.era.coast.Q φ.canvas φ.duty ht.le φ.price.roam
end

end daylight
section
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x β w e L z h y M a : ℝ} {T : Tube G S}
    {J : ChartRatio G} {Y : Lantern G S} {D : Allocation G S x w}
section night
variable {C : Family G} {i k N p n : ℕ} {ξ : Purse}
    {g : Course C N p k} {B : Binding C} (ht : i<k)
    {P : Rep G (C.S.side (i+1) p)} {R : Rep G (C.S.side i p)}

local notation "X" => Atlas.clim C.path.levels i
local notation "V" => Atlas.clim C.path.levels (i+1)
local notation "U" => Atlas.clim C.path.levels k
local notation "L1" => ξ.era
local notation "E" => ξ.era.coast.e
local notation "Fn" => Ship.allowance C.path.levels 2 k
local notation "K" => kinetics U
set_option quotPrecheck false
local notation "BT"=> tunnel B N i p
local notation "St" => C.path.levels.clock.op i p
variable (hn : i<k)
include ht
lemma shutters_Sky {σ α π δ t : ℝ} (hw : Tissue P σ α π δ t) (hP : g.changeβ (i+1)=P.beta) {w} {J} (Y : Lantern G St) (D : Allocation G St (retime X) w)
    (A : Boosted BT (tell B i) (retime X)) (hx : TimeBand L1 ξ.goal (C.path.levels.clock.op i p).patch.L P.p R.p X V U n)
    (Hp : Station.widthSky C.path.levels ξ.band k ≤ i) (F : Points n) (hp : Station.FitSky C.path.levels ξ.band k F)
    (r : ℝ) (hr : 0 < r) (hh : Coupler BT Y J D P.beta) (hv : Kiln P R A hx.lamp J Y D r E (Perch.gas (L1).coast V)⁻¹ 1 (K/16) (K/4) K) :
    ∃ Z, DarkSky ((show i+1≤k from ht).trans g.allow) g F ξ.era ξ.band r P R Z:= by
  let θ := readersSky (C:=C) (b:=ξ.band) (p:=p) F g.allow ((show i+1≤k from ht).trans g.allow); let u:= readersSky (C:=C) (b:=ξ.band) (p:=p) F g.allow (ht.le.trans g.allow)
  have hH : u=(C.path.levels.clock.op i p).ratio.parent ∘ θ:= liftHSky F (ht:=ht) (g:=g)
  obtain ⟨ι,hι,S,Q,H,hS,hl⟩:= hv.compile_
  obtain ⟨Z,hZ,hV⟩:= hl _ _ _ θ u hH
  refine ⟨Z,⟨?_⟩⟩
  intro α β hα hβ G' I z hz hy hz' hB
  let P₀:= pearls P R Y A hx.lamp hH G'; let Y₀:=Gel.freezeKey I; let m := (Perch.gas (L1).coast V)⁻¹
  let Λ':= picture P R S Y₀ P₀ A hx.lamp hH; let T:=bequeath Λ' A
  have hyx : 0≤ z*Perch.w V:= mul_nonneg hz (Real.exp_pos _).le
  have hx':1 ≤ m:= (one_le_inv₀ (gas_le _ _).1).2 (gas_le _ _).2
  let L' i := Glaze P R S Y₀ P₀ A hx.lamp hH (fun _=>False) i
  obtain ⟨hl,hv'⟩:= hx.night z hz hy
  have he:= v_reward P R S I P₀ A hx.lamp hH hw (fun _=>False) G' hh H (hV _ _ _ _ _ hw.status) hr (l:=1) le_rfl hx' hz' hB hyx
    (acts P R Y A hx.lamp hH G') (Towering.covers _ hx.lower) (Towering.tallies hx.lower) (ancestor_PSky F g.allow Hp _ hp)
    hS (pains P R Y A hx.lamp hH G' hz'.bulk (Towering.covers _ hx.lower) (fun _=>hr) le_rfl)
    (mul_nonneg (mul_nonneg zero_le_one (Real.exp_pos _).le) hz) hZ hl hx.cadence hx.tempo hv'
  refine ⟨_,inferInstance,T,hP.symm ▸ he.1,?_⟩
  have hT:L'=fun _=>False:= by
    funext i; refine propext ⟨fun h=>?_, False.elim⟩
    obtain ⟨h₁,h₂⟩:=h; obtain ⟨j|j,hj⟩:= i.val.property.1.1
    · have he:= Finset.mem_toLeft.mpr hj; rw [h₁] at he; exact Finset.notMem_empty _ he
    exact h₂ j (Finset.mem_toRight.mpr hj)
  rw [← hT]; exact he.2
end night
end
section exports
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
     YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory Bid Display Display.Docking Filter AnalyticBridge.LocalGaussianLaws Local RG.Supply Next.Rank.Station Tree
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} (B : Binding C) {N i k p : ℕ} (J : ChartRatio G) (ξ : Purse)
    (m : C.Makes) {w l a c : ℝ} {F : Course C N p k} (H : ShowHoursSky J B ξ k w l a)
    (V : (i:ℕ)→ Rep G (C.side i p)) (O : LaunchSky C k ξ w c) (A : WhipSky B J ξ H O F V (Station.widthSky C.path.levels ξ.band k) le_rfl)

include A

include m

end exports
end YM.PhysicalNext.InteractingRank.Soft
