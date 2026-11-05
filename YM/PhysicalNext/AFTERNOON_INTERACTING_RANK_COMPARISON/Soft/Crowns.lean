import YM.Next.MULTISOURCE.Spill
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Agate
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Boxes
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Spread
/-! # Export actual Choir over *new* kiln & soft Whip

Same Audience and Dark definitions of strong receipt. New composition
law via stage-1 argument (Festival/Furnace) with actual softened but
real data. -/
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

section
include φ m
lemma daypay_ (Y : Lantern G St) (s : Site (C.side (i+1) p)) (U : Config G (C.side i p)) (A : Stores St) (hp : Positioned (retime XL) A U) (j : Streak Y.park) :
    (viewer BT A (retime XL) j.wood j.tag U).real (Prod.snd ⁻¹' away (parasol s (ξ.era.coast.Q*walls XF)) (haze G XL P.beta (C.path.levels.clock.op i p).patch.L/2)) ≤ XL^(-(1:ℝ)):= by
  rw [calendar_warm,← φ.fits]
  let h:= φ.price; let J:= ships B N i p m (lt_of_lt_of_le ht g.allow)
  refine (shade_auth A j.wood XL Y.χ s ξ.era.coast.Q U BT j.tag h.steady.visible h.steady.sparks h.strong.cash h.heat le_rfl (h.strong.ribbon St BT rfl J (B.sized i p) ?_ _ _ j.tag U hp _)).2
  exact hot_fits ξ.era.coast.Q φ.canvas φ.duty ht.le φ.price.roam
end

set_option synthInstance.maxSize 400 in
lemma gala_ {σ α π δ t : ℝ} (hw : Tissue P σ α π δ t) {w} (J : ChartRatio G) (Y : Lantern G St) (D : Allocation G St (retime XL) w)
    (A : Boosted BT (tell B i) (retime XL)) (hx : TimeBand ξ.era ξ.goal (C.path.levels.clock.op i p).patch.L P.p R.p XL XF τ n)
    (hp : Station.Allowed C.path.levels ξ.band k) (he : 30≤ξ.horizon) (X : Points n) (hf : Station.Fit C.path.levels ξ.band k X) (hn : n ≤ 2)
    (r : ℝ) (hr : 0 < r) (hc : Coupler BT Y J D P.beta) (hv : Kiln P R A hx.lamp J Y D r E M IX (K/16) (K/4) K) :
    ∃ Z,Audience (S:=ξ.era) (φ.approve m X Y) Z r ξ.goal := by
  let θ := readers (C:=C) (b:=ξ.band) (p:=p) X g.allow ((show i+1≤k from ht).trans g.allow)
  let u := readers (C:=C) (b:=ξ.band) (p:=p) X g.allow (ht.le.trans g.allow)
  have hu : u=(C.path.levels.clock.op i p).ratio.parent ∘ θ:= liftH X (g:=g) (ht:=ht)
  obtain ⟨ρ,hρ,S,Λ,H,hS,hl⟩:= hv.compile_
  obtain ⟨Z,hZ,hV⟩:= hl _ _ _ θ u hu
  refine ⟨Z,⟨?_⟩⟩
  intro W hW hP ι κ hι hκ G' I z hz hy hz' hB
  dsimp only
  let P₀:= pearls P R Y A hx.lamp hu G'; let F:= S_Sunrise φ Y X W hW A hx.lamp; let Z0:= Sum.elim P₀ F; let Y₀:=Gel.freezeKey I
  let Λ₀:= picture P R S Y₀ Z0 A hx.lamp hu; let Q:= bequeath Λ₀ A
  let L:= Line ξ.era ξ.goal z τ
  have hT: 1 ≤ L:=le_max_left ..
  let v:=fuel ξ.era ξ.goal τ z
  have he' : L≤ IX:= noInflate ξ.era _ _ _ hz
  let h := fun _ : (Ship.yard C ξ.band g.allow p).Cell × Fin n=>r
  let w:=salary E*bill (-4) τ
  have hg: Spot R F lightcast BT L h E (w+w):= by
    refine purchases P R Y A hx.lamp hu W XL _ _ (s_light_size φ X W hW) hP (Towering.covers _ hx.upper) (fun _=>hr) hT φ.price.steady.visible (φ.fits ▸ φ.price.steady.sparks) ?_
    intro i V B hh j; exact (mul_le_mul he' (daypay_ φ m Y _ _ _ hh j) (ENNReal.toReal_nonneg) (zero_le_one.trans (le_max_left ..))).trans hx.infl
  have ℓ : 0 ≤ GAS XF := (Real.exp_pos _).le
  have hG : 1 ≤ (GAS XL^2)⁻¹:= (one_le_inv₀ (pow_pos (gas_le _ _).1 _)).2 (pow_le_one₀ (gas_le _ _).1.le (gas_le _ _).2)
  obtain ⟨hl,hv₀⟩:= hx.day z hz hy
  have hs : Light P (Sum.elim G' W) I h E (z+bill (-4) τ) (GAS XF):= ⟨Shine.plus G' W (show Shine .. from hz'.bulk) hP,hz'.forced⟩
  have hE:= v_reward P R S I Z0 A hx.lamp hu hw sparklers (Sum.elim G' W) hc H (hV _ _ _ _ _ hw.status) hr hT hG hs hB ℓ
     (joined P₀ F (acts P R Y A hx.lamp hu G') (enlightens P R Y A hx.lamp hu W XL _ _ (s_light_size φ X W hW))) (Towering.covers _ hx.upper) (Towering.tallies hx.upper)
     (ancestor_P X g.allow ((Station.wider ..).trans φ.duty) _ hf) (discounted R S hS he')
     (packed_both P₀ F (fun _=>False) lightcast _ _ v (pains P R Y A hx.lamp hu G' hz'.bulk (Towering.covers _ hx.upper) (fun _=>hr) hT) hg le_rfl) (fuel_nn _ _ _ _ hz)
     (repair_lower R _ (fun _=>hr) hZ he') hl hx.cadence hx.tempo hv₀
  exact ⟨_,inferInstance,Q,Glaze P R S Y₀ Z0 A hx.lamp hu sparklers, φ.fits.symm ▸ hE.1,hE.2,s_in_stalls φ Y X W hW A hx.lamp hg (fun _=>hr) P₀ S Y₀ hn he hp hf m⟩
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
lemma shutters_ {σ α π δ t : ℝ} (hw : Tissue P σ α π δ t) (hP : g.changeβ (i+1)=P.beta) {w} {J} (Y : Lantern G St) (D : Allocation G St (retime X) w)
    (A : Boosted BT (tell B i) (retime X)) (hx : TimeBand L1 ξ.goal (C.path.levels.clock.op i p).patch.L P.p R.p X V U n)
    (Hp : Station.width C.path.levels ξ.band k ≤ i) (F : Points n) (hp : Station.Fit C.path.levels ξ.band k F)
    (r : ℝ) (hr : 0 < r) (hh : Coupler BT Y J D P.beta) (hv : Kiln P R A hx.lamp J Y D r E (Perch.gas (L1).coast V)⁻¹ 1 (K/16) (K/4) K) :
    ∃ Z, Dark ((show i+1≤k from ht).trans g.allow) g F ξ.era ξ.band r P R Z:= by
  let θ := readers (C:=C) (b:=ξ.band) (p:=p) F g.allow ((show i+1≤k from ht).trans g.allow); let u:= readers (C:=C) (b:=ξ.band) (p:=p) F g.allow (ht.le.trans g.allow)
  have hH : u=(C.path.levels.clock.op i p).ratio.parent ∘ θ:= liftH F (ht:=ht) (g:=g)
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
    (acts P R Y A hx.lamp hH G') (Towering.covers _ hx.lower) (Towering.tallies hx.lower) (ancestor_P F g.allow Hp _ hp)
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
    (m : C.Makes) {w l a c : ℝ} {F : Course C N p k} (H : ShowHours J B ξ k w l a)
    (V : (i:ℕ)→ Rep G (C.side i p)) (O : Launch C k ξ w c) (A : Whip B J ξ H O F V (Station.width C.path.levels ξ.band k) le_rfl)
local notation "t"=> Atlas.clim C.path.levels k
include A
lemma loomWorks (hi : Station.width C.path.levels ξ.band k ≤ i) (ht : i<k) {n : ℕ} (hn : n≤2):
    TimeBand ξ.era ξ.goal (C.path.levels.clock.op i p).patch.L (V (i+1)).p (V i).p (Atlas.clim C.path.levels i) (Atlas.clim C.path.levels (i+1)) t n:= by
  have hf: Station.width C.path.levels ξ.band k ≤ i+1:= hi.trans (Nat.le_succ _)
  have hx : (V i).p= _:= (A.outer i hi ht.le).1.warm.used
  have hX : (V (i+1)).p=_:= (A.outer _ hf ht).1.warm.used
  rw [(sizes_at ξ O.coup hi ht p).1]; exact H.flash.clamp n hn _ (O.coup.court i hi ht.le) _ (O.coup.court _ hf ht) _ _ (hX ▸ rfl) (hx ▸ rfl)
include m
theorem s_choir {n : ℕ}(X : Points n)(hz : Fit C.path.levels ξ.band k X)(hn : n≤2) : Choir ξ F V (short B N p) X:= by
  constructor
  · intro i hi hj; dsimp only; obtain ⟨b,z,h⟩:= alloc V A hi hj
    have hL:= (Station.wider ..).trans hj
    obtain ⟨hp,T,Y,D,hV,hW⟩:= (A.stokes i hL hi).heats
    have hv := loomWorks B J ξ H V O A hL hi hn
    exact ⟨h.approve m X Y,gala_ h m (A.outer _ (hL.trans (Nat.le_succ i)) hi).1.pets J Y D T hv O.coup.heft (Posts.mile H.flash) X hz hn _ (Real.exp_pos _) hV (hW _ (Real.exp_pos _)).1⟩
  intro i hp hj; have hi:i<k:= lt_of_lt_of_le hj (before ..)
  have hv:= loomWorks B J ξ H V O A hp hi hn
  obtain ⟨hu,T,Y,D,hV,hW⟩:=(A.stokes i hp hi).heats
  obtain ⟨hx,hQ⟩:= A.outer (i+1) (hp.trans (Nat.le_succ i)) hi
  exact shutters_ hi hx.pets hQ.coupling Y D T hv hp X hz _ (Real.exp_pos _) hV (hW _ (Real.exp_pos _)).2
end exports
end YM.PhysicalNext.InteractingRank.Soft
