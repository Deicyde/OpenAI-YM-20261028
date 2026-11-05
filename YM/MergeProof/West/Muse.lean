import YM.MergeProof.West.AudienceM
import YM.MergeProof.West.Moon
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Crowns


/-! # Export actual Choir over *new* kiln & soft Whip

Same Audience and Dark definitions of strong receipt. New composition
law via stage-1 argument (Festival/Furnace) with actual softened but
real data. -/
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
    (φ : Spear B g ξ ht o z P R) (m : C.Makes)
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
lemma galaFt {σ α π δ t : ℝ} (hw : Tissue P σ α π δ t) {w} (J : ChartRatio G) (Y : Lantern G St) (D : Allocation G St (retime XL) w)
    (A : Boosted BT (tell B i) (retime XL)) (hx : TimeBand ξ.era ξ.goal (C.path.levels.clock.op i p).patch.L P.p R.p XL XF τ n)
    (hp : Station.Allowed C.path.levels ξ.band k) (he : 6*n+3 ≤ ξ.horizon/(3+2*n)) (X : Points n) (hf : Station.Fit C.path.levels ξ.band k X) 
    (r : ℝ) (hr : 0 < r) (hc : Coupler BT Y J D P.beta) (hv : Kiln P R A hx.lamp J Y D r E M IX (K/16) (K/4) K) :
    ∃ Z,AudFt (S:=ξ.era) (φ.a_pprove m X Y) Z r ξ.goal := by
  let θ := readers (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i+1≤k from ht).trans g.allow)
  let u := readers (C:=C) (b:=ξ.band) (p:=p) X g.allow (ht.le.trans g.allow)
  have hu : u=(C.path.levels.clock.op i p).ratio.parent ∘ θ:= liftH X (g:=g) (ht:=ht)
  obtain ⟨ρ,hρ,S,Λ,H,hS,hl⟩:= hv.compile_
  obtain ⟨Z,hZ,hV⟩:= hl _ _ _ θ u hu
  refine ⟨Z,⟨?_⟩⟩
  intro W hW hP ι κ hι hκ G' I z hz hy hz' hB
  dsimp only
  let P₀:= pearls P R Y A hx.lamp hu G'; let F:= S_Sunrise_ft φ Y X W hW A hx.lamp; let Z0:= Sum.elim P₀ F; let Y₀:=Gel.freezeKey I
  let Λ₀:= picture P R S Y₀ Z0 A hx.lamp hu; let Q:= bequeath Λ₀ A
  let L:= Line ξ.era ξ.goal z τ
  have hT: 1 ≤ L:=le_max_left ..
  let v:=fuel ξ.era ξ.goal τ z
  have he' : L≤ IX:= noInflate ξ.era _ _ _ hz
  let h := fun _ : (Ship.yard C ξ.band g.allow p).Cell × Fin n=>r
  let w:=salary E*bill (-4) τ
  have hg: Spot R F lightcast BT L h E (w+w):= by
    refine purchases P R Y A hx.lamp hu W XL _ _ (s_light_size_ft φ X W hW) hP (Towering.covers _ hx.upper) (fun _=>hr) hT φ.price.steady.visible (φ.fits ▸ φ.price.steady.sparks) ?_
    intro i V B hh j; exact (mul_le_mul he' (daypay_ φ m Y _ _ _ hh j) (ENNReal.toReal_nonneg) (zero_le_one.trans (le_max_left ..))).trans hx.infl
  have ℓ : 0 ≤ GAS XF := (Real.exp_pos _).le
  have hG : 1 ≤ (GAS XL^2)⁻¹:= (one_le_inv₀ (pow_pos (gas_le _ _).1 _)).2 (pow_le_one₀ (gas_le _ _).1.le (gas_le _ _).2)
  obtain ⟨hl,hv₀⟩:= hx.day z hz hy
  have hs : Light P (Sum.elim G' W) I h E (z+bill (-4) τ) (GAS XF):= ⟨Shine.plus G' W (show Shine .. from hz'.bulk) hP,hz'.forced⟩
  have hE:= v_reward P R S I Z0 A hx.lamp hu hw sparklers (Sum.elim G' W) hc H (hV _ _ _ _ _ hw.status) hr hT hG hs hB ℓ
     (joined P₀ F (acts P R Y A hx.lamp hu G') (enlightens P R Y A hx.lamp hu W XL _ _ (s_light_size_ft φ X W hW))) (Towering.covers _ hx.upper) (Towering.tallies hx.upper)
     (ancestor_P X g.allow ((Station.wider ..).trans φ.duty) _ hf) (discounted R S hS he')
     (packed_both P₀ F (fun _=>False) lightcast _ _ v (pains P R Y A hx.lamp hu G' hz'.bulk (Towering.covers _ hx.upper) (fun _=>hr) hT) hg le_rfl) (fuel_nn _ _ _ _ hz)
     (repair_lower R _ (fun _=>hr) hZ he') hl hx.cadence hx.tempo hv₀
  exact ⟨_,inferInstance,Q,Glaze P R S Y₀ Z0 A hx.lamp hu sparklers, φ.fits.symm ▸ hE.1,hE.2,s_in_stalls_ft φ Y X W hW A hx.lamp hg (fun _=>hr) P₀ S Y₀ he hp hf m⟩
end daylight
end YM.PhysicalNext.InteractingRank.Soft
