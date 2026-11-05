import YM.MergeProof.West.Muse
import YM.TraceExtension.Prom.Front.West.AudienceM
import YM.TraceExtension.Prom.Front.West.Ballast
import YM.TraceExtension.Prom.Front.West.Horns
import YM.TraceExtension.Prom.Front.West.Moon
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.Throne
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Flux.Grader
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
import YM.TraceExtension.Prom.Port.Brocade
import YM.TraceExtension.Prom.Port.Soft.Crowns
import YM.TraceExtension.Prom.Port.Soft.Spear
/-!
  Variant of YM.MergeProof.West.Muse for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open YM.Next.Rank.Tapes.West
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

set_option synthInstance.maxSize 400 in
lemma galaFtSky {σ α π δ t : ℝ} (hw : Tissue P σ α π δ t) {w} (J : ChartRatio G) (Y : Lantern G St) (D : Allocation G St (retime XL) w)
    (A : Boosted BT (tell B i) (retime XL)) (hx : TimeBand ξ.era ξ.goal (C.path.levels.clock.op i p).patch.L P.p R.p XL XF τ n)
    (hp : Station.AllowedSky C.path.levels ξ.band k) (he : 6*n+3 ≤ ξ.horizon/(3+2*n)) (X : Points n) (hf : Station.FitSky C.path.levels ξ.band k X)
    (r : ℝ) (hr : 0 < r) (hc : Coupler BT Y J D P.beta) (hv : Kiln P R A hx.lamp J Y D r E M IX (K/16) (K/4) K) :
    ∃ Z,AudFtSky (S:=ξ.era) (φ.a_pprove m X Y) Z r ξ.goal := by
  let θ := readersSky (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i+1≤k from ht).trans g.allow)
  let u := readersSky (C:=C) (b:=ξ.band) (p:=p) X g.allow (ht.le.trans g.allow)
  have hu : u=(C.path.levels.clock.op i p).ratio.parent ∘ θ:= liftHSky X (g:=g) (ht:=ht)
  obtain ⟨ρ,hρ,S,Λ,H,hS,hl⟩:= hv.compile_
  obtain ⟨Z,hZ,hV⟩:= hl _ _ _ θ u hu
  refine ⟨Z,⟨?_⟩⟩
  intro W hW hP ι κ hι hκ G' I z hz hy hz' hB
  dsimp only
  let P₀:= pearls P R Y A hx.lamp hu G'; let F:= S_Sunrise_ftSky φ Y X W hW A hx.lamp; let Z0:= Sum.elim P₀ F; let Y₀:=Gel.freezeKey I
  let Λ₀:= picture P R S Y₀ Z0 A hx.lamp hu; let Q:= bequeath Λ₀ A
  let L:= Line ξ.era ξ.goal z τ
  have hT: 1 ≤ L:=le_max_left ..
  let v:=fuel ξ.era ξ.goal τ z
  have he' : L≤ IX:= noInflate ξ.era _ _ _ hz
  let h := fun _ : (Ship.yardSky C ξ.band g.allow p).Cell × Fin n=>r
  let w:=salary E*bill (-4) τ
  have hg: Spot R F lightcast BT L h E (w+w):= by
    refine purchases P R Y A hx.lamp hu W XL _ _ (s_light_size_ftSky φ X W hW) hP (Towering.covers _ hx.upper) (fun _=>hr) hT φ.price.steady.visible (φ.fits ▸ φ.price.steady.sparks) ?_
    intro i V B hh j; exact (mul_le_mul he' (daypay_Sky φ m Y _ _ _ hh j) (ENNReal.toReal_nonneg) (zero_le_one.trans (le_max_left ..))).trans hx.infl
  have ℓ : 0 ≤ GAS XF := (Real.exp_pos _).le
  have hG : 1 ≤ (GAS XL^2)⁻¹:= (one_le_inv₀ (pow_pos (gas_le _ _).1 _)).2 (pow_le_one₀ (gas_le _ _).1.le (gas_le _ _).2)
  obtain ⟨hl,hv₀⟩:= hx.day z hz hy
  have hs : Light P (Sum.elim G' W) I h E (z+bill (-4) τ) (GAS XF):= ⟨Shine.plus G' W (show Shine .. from hz'.bulk) hP,hz'.forced⟩
  have hE:= v_reward P R S I Z0 A hx.lamp hu hw sparklers (Sum.elim G' W) hc H (hV _ _ _ _ _ hw.status) hr hT hG hs hB ℓ
     (joined P₀ F (acts P R Y A hx.lamp hu G') (enlightens P R Y A hx.lamp hu W XL _ _ (s_light_size_ftSky φ X W hW))) (Towering.covers _ hx.upper) (Towering.tallies hx.upper)
     (ancestor_PSky X g.allow ((Station.widerSky ..).trans φ.duty) _ hf) (discounted R S hS he')
     (packed_both P₀ F (fun _=>False) lightcast _ _ v (pains P R Y A hx.lamp hu G' hz'.bulk (Towering.covers _ hx.upper) (fun _=>hr) hT) hg le_rfl) (fuel_nn _ _ _ _ hz)
     (repair_lower R _ (fun _=>hr) hZ he') hl hx.cadence hx.tempo hv₀
  exact ⟨_,inferInstance,Q,Glaze P R S Y₀ Z0 A hx.lamp hu sparklers, φ.fits.symm ▸ hE.1,hE.2,s_in_stalls_ftSky φ Y X W hW A hx.lamp hg (fun _=>hr) P₀ S Y₀ he hp hf m⟩
end daylight
end YM.PhysicalNext.InteractingRank.Soft
