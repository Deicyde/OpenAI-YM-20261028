import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Leashes
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Plough
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stocking
/-!
# One purchased step of the adaptive Bush

`EpochThaw`: unmarked prerequisites, before any Raw marker
expansions. Includes gas-free sector prep (obtained in Opacity/), and
still scalar log equations and physical β,E candidate. Does
NOT presume emptiness of unmarked fine K. Must hold along same family.
Keep all calibration, path, and proof alignments literal.
`spends`,`earns_step`: then produce actual Stack for one step.
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
local notation "x₀"=> Atlas.clim C.path.levels k
local notation "Υ"=> C.path.levels.params k
local notation "v"=> Perch.gas ξ.era.coast
local notation "ℓ"=> C.path.levels.clock.factor (C.path.levels.clock.J k)
local notation "St"=> C.path.levels.clock.op i p
local notation "L"=> ξ.band
local notation "HP"=> C.path.levels.clock.hatBeta
local notation "WL"=> Station.width C.path.levels ξ.band k
local notation "XT"=> tunnel B N i p
local notation "X"=> Atlas.clim C.path.levels i
local notation "Y"=> Atlas.clim C.path.levels (i+1)
local notation "Ec"=> load ξ.era

variable (H : ShowHours J B ξ k w l r)
/-- Unmarked call from before step. Q shell in *R-coordinates on this data*.
Inactive K fields of this Q are padding (but still require
ThresholdE, so may need to accomodate equivariance). β update
input red; root scalar relates unmarked gas
and existing projection/boundary, not solving renormalization here. -/
structure EpochThaw (P : Rep G (C.side (i+1) p)) (hc : i<k) (hb : WL ≤ i) (Zs : Bush B J ξ (N:=N) H P hc (hb.trans (Nat.le_succ i))) : Prop where
  heat : ∀ A:Boosted XT (tell B i) (retime X),
    ∃ Y₀: Lantern G St,Y₀.χ=Chi.canonical ∧ Y₀.hood=dressing G C.path.levels i p r ∧
    ∃ (D : Allocation G St (retime X) l) (Q : Rep G (C.side i p)),
      Q.path=(C.path.rep N p i).path ∧ Q.clip=(C.path.levels.params i).clip ∧
      Q.p= Paint.inbox C i (H.oldPrices i hc.le hb) ∧
      |P.beta-Q.beta|≤ (Υ).drift+ shear G ℓ ∧
      ThresholdE Q (C.path.levels.params i).width (C.path.levels.params i).paths (C.path.levels.clock.loopCap i) (C.path.levels.clock.allowance i) ∧
      ∀ hs : 25*radiusB (retime X)+30 ≤ Q.p.B,∃ ι α:Type, ∃ (_:Fintype ι) (_:Fintype α), ∃ (p' : ι→Zest G St (retime X) Y₀.park Q.p.threshold) (V : Config G (C.side i p)→ℝ) (E : α→ Rim Q.p.threshold G (C.side i p)),
        Opacity P Q p' A hs Zs.rated V (J:=J) (D:=D) Ec (acres ξ X Y) (Line ξ.era ξ.goal 0 x₀) (tinder ξ x₀) ∧
        Resin P Q p' A hs Zs.rated V E Ec (kinetics x₀)

section
-- end products
variable (hi : i<k) (hh : Station.width C.path.levels ξ.band k ≤ i) {P : Rep G (C.side (i+1) p)}
structure Stack (P : Rep G (C.side (i+1) p)) (Q : Rep G (C.side i p)) : Prop where
  advance : Bush B J ξ (N:=N) H Q hi.le hh
  warmth : |P.beta-Q.beta|≤ (Υ).drift+ shear G ℓ
  pushes : Q.eval=(C.path.levels.clock.op i p).push P.beta P.eval
  dawn : GalaBurn B (N:=N) J ξ l r k P Q
  eve : ShadingBurn B (N:=N) J ξ l r k P Q

variable (O : Bush B J ξ H (N:=N) (i:=i+1) P (show i+1≤k from hi) (hh.trans (Nat.le_succ i)))
    (hp : Corridor C.path.levels ξ.band ξ k)
include hi hh O hp
lemma settled_prices (t:ℝ) (hc : |P.beta-t|≤ (Υ).drift+ shear G ℓ) :
    |t-X| ≤ x₀/8 + (k-i : ℕ)* ((Υ).drift+2*shear G ℓ):= by
  let d:=shear G ℓ; have hs:0≤d:= Work.E04.shift_nonneg ..
  have h:Y=X+d:= by
    rw [calendar_warm]; unfold betaF; rw [show C.S.block i=ℓ from (sizes_at ξ hp hh hi p).1]; rfl
  have h₁ : (↑(k-i):ℝ)=↑(k-(i+1))+1:= by exact_mod_cast (show k-i=k-(i+1)+1 by omega)
  have hx:= O.βgap; rw [h] at hx; rw [h₁]; have hw := abs_le.mp hx; have hz:=abs_le.mp hc; apply abs_le.mpr; constructor <;> linarith only [hw.1,hw.2,hz.1,hz.2,hs]
lemma coast_lease (Q : Rep G (C.side i p)) (h₁: Q.p= Paint.inbox C i (H.oldPrices i hi.le hh)) :
    25*radiusB (retime X)+30 ≤ Q.p.B ∧ Lease (St).patch.L P.p Q.p (load ξ.era) (acres ξ X Y) (Line ξ.era ξ.goal 0 x₀) (tinder ξ x₀) (kinetics x₀) (v Y):= by
  have h':Station.width C.path.levels ξ.band k≤ i+1:=hh.trans (Nat.le_succ i)
  obtain ⟨hX,hY⟩:= sizes_at ξ hp hh hi p
  have hx:=hp.court _ hh hi.le; have hy:=hp.court (i+1) h' hi
  have hU:P.p.B= walls Y:= O.used ▸ rfl
  have hP:= H.flash.clamp 0 (by decide) X hx Y hy P.p Q.p hU (h₁ ▸ rfl)
  have hθ:= H.adaptive.lease P.p Q.p X Y hx hy hU (h₁▸ rfl) hP.upper.square
    (show P.p.supportExponent=(Υ).supportExponent from O.used ▸ (show (Paint.inbox ..).supportExponent=(Υ).supportExponent from congr_arg Stage.supportExponent (common_era ξ hp h' hi)))
    (h₁ ▸ (show _ from congr_arg Stage.supportExponent (common_era ξ hp hh hi.le)))
  exact ⟨hP.lamp,(hX.symm ▸ hθ)⟩
include M in
lemma holding_graph (hN : k ≤ N) :∃ _ : Boosted XT (tell B i) (retime X),∀ (Y':Lantern G St), Y'.hood=dressing G C.path.levels i p r →∀ D:Allocation G St (retime X) l, Coupler XT Y' J D P.beta:= by
  have h':Station.width C.path.levels ξ.band k≤ i+1:=hh.trans (Nat.le_succ i)
  obtain ⟨hX,hY⟩:= sizes_at ξ hp hh hi p
  have hx:=hp.court _ hh hi.le; have hy:=hp.court (i+1) h' hi
  let W:=initials B.prices (Λ).clock.stage (Λ).clock.kernel ((Λ).clock.J k) ((Λ).clock.J k) (G:=G)
  have hw : tell B i=W:= by unfold tell W;rw [hp.heft.plateau i hh hi.le,hp.heft.plateau (i+1) h' hi]
  obtain ⟨A,-,-,hv⟩:= H.flash.stamp X hx _ _ St XT hX hY (C.path.levels.blocks i p).branches (H.yard i hh hi p) (show W.Funds St XT from hw ▸ ships B N i p M (hi.trans_le hN))
  let T : Boosted XT (tell B i) (retime X):= hw.symm ▸ A
  refine ⟨T,fun Y' he D=> hv _ ?_ _ (bush_pos B J ξ hp O) D⟩
  rw [he]; unfold dressing; rw [hX]
include M in
lemma spends (hN : k ≤ N) (Y': Lantern G St) (h₃ : Y'.χ=Chi.canonical) (h₄ : Y'.hood=dressing G C.path.levels i p r) (T : Boosted XT (tell B i) (retime X)) (D : Allocation G St (retime X) l) (Q : Rep G (C.side i p))
    (hQ : Q.path=(C.path.rep N p i).path) (hQ' : Q.clip=(C.path.levels.params i).clip) (h₁ : Q.p= Paint.inbox C i (H.oldPrices i hi.le hh)) (h₂ : |P.beta-Q.beta|≤ (Υ).drift+ shear G ℓ)
    (h5 : ThresholdE Q (C.path.levels.params i).width (C.path.levels.params i).paths (C.path.levels.clock.loopCap i) (C.path.levels.clock.allowance i))
    (h6 : ∀ hs : 25*radiusB (retime X)+30 ≤ Q.p.B,∃ ι α:Type, ∃ (_:Fintype ι) (_:Fintype α), ∃ (p' : ι→Zest G St (retime X) Y'.park Q.p.threshold) (V : Config G (C.side i p)→ℝ) (E : α→ Rim Q.p.threshold G (C.side i p)),
        Opacity P Q p' T hs O.rated V (J:=J) (D:=D) Ec (acres ξ X Y) (Line ξ.era ξ.goal 0 x₀) (tinder ξ x₀) ∧
        Resin P Q p' T hs O.rated V E Ec (kinetics x₀)) :∃ Q', Stack (N:=N) B J ξ H hi hh P Q' ∧ Q'.beta=Q.beta:=by
  obtain ⟨A,hv⟩:= holding_graph B M J ξ H hi hh O hp hN
  obtain ⟨hm,hL⟩:= coast_lease B J ξ H hi hh O hp Q h₁
  obtain ⟨ι,α,hι,hα,V,R,E,Ho,Hr⟩:=h6 hm
  let G':=germinates P Q V T hm O.rated E
  have hω := sounded P Q V T hm O.rated E Ho hL Hr h5 (acres_pay ..)
  refine ⟨G',⟨⟨h₁,hQ,hQ',settled_prices B J ξ H hi hh O hp _ h₂,hω⟩,h₂,perceived P Q V T hm O.rated E Ho hL Hr (hv Y' h₄ D) hω,?_,?_⟩,rfl⟩
  exact fun _=> ⟨Y',h₃,h₄,fun _=>⟨D,fireplace _ _ _ _ _ _ _ Ho hL Hr le_rfl (le_max_left ..) le_rfl (Real.exp_pos _)⟩⟩
  exact fun _=> ⟨Y',h₃,h₄,fun _=>⟨D, fireplace _ _ _ _ _ _ _ Ho hL Hr (show ξ.era.coast.e≤Ec by unfold load; linarith only) (le_max_right ..) (le_max_left 1 _) (Real.exp_pos _)⟩⟩
include M in
lemma earns_step (hN : k ≤ N) (ht : EpochThaw B J ξ H P hi hh O) : ∃ Q, Stack (N:=N) B J ξ H hi hh P Q:=by
  obtain ⟨T,hT⟩:= holding_graph B M J ξ H hi hh O hp hN
  obtain ⟨Y',h₃,h₄,D,Q,hQ,hQ',h₁,h₂,h5,h6⟩:=ht.heat T
  obtain ⟨Q',h,h'⟩:= spends B M J ξ H hi hh O hp hN _ h₃ h₄ _ D _ hQ hQ' h₁ h₂ h5 h6; exact ⟨Q',h⟩
end
end YM.PhysicalNext.InteractingRank
