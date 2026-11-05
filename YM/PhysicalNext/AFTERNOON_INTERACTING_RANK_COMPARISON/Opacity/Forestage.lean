import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Leashes
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Pergola
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stocking
/-!
# F oil apparatus for this actual Course

One prescribed chart for unmarked portion here, built on P, and
*all* Rep candidates Q at this BudgetPoint. `Kinesis`: input includes true
ThresholdE and scalar/Rim against unmarked gas against these labels. Not
postulating any estimate on marked gas. `sawn`: package for use (thermal
retiming). Origins needed separately.
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
local notation "s"=> Atlas.clim C.path.levels k
local notation "Υ"=> C.path.levels.params k
local notation "b"=> C.path.levels.clock.J k
local notation "ℓ"=> C.path.levels.clock.factor (C.path.levels.clock.J k)
local notation "St"=> C.path.levels.clock.op i p
local notation "H₀"=> ξ.band
local notation "K0"=> Station.width C.path.levels ξ.band k
local notation "t"=> tunnel B N i p
local notation "X"=> Atlas.clim C.path.levels i
local notation "y"=> Atlas.clim C.path.levels (i+1)
-- Inputs
variable (H : ShowHours J B ξ k w l r) (Z : Marquee B ξ J l r k) (O : Corridor C.path.levels ξ.band ξ k) (hN : k ≤ N)
    {P : Rep G (C.side (i+1) p)} (hi : i<k)(hl : Station.width C.path.levels ξ.band k ≤ i) (hP : Bush B J ξ (N:=N) H P hi (hl.trans (Nat.le_succ i)))
-- position frame independent of P amplitude; actual `Kept` ties projections.
def tabloid (hc : i<k) (hz : Station.width C.path.levels ξ.band k≤ i) (P : Rep G (C.side (i+1) p)): Dyed G St := ⟨P,t,Chi.canonical,J,dressing G C.path.levels i p r, Paint.inbox C i (H.oldPrices i hc.le hz),
    (Orchard.canopy St).table 0, Classical.choice (show Nonempty (St).Choices from by obtain ⟨v,h⟩:= exists_alive (C.path.levels.blocks i p).branches (1:Config G (C.side (i+1) p)); exact ⟨v⟩)⟩
local notation "Ψ"=> tabloid B J ξ H hi hl P (N:=N)
include hN M hP Z O hl in
lemma fitPost : Seeks (Ψ) (tell B i) r X:=by
  obtain ⟨hL,hJ⟩:= sizes_at ξ O hl hi p
  have he : i+1≤k := hi; have hf : K0≤ i+1:=hl.trans (Nat.le_succ i); let j:=C.path.levels.clock.J k
  have hT := Z.great.timing X (O.court i hl hi.le); obtain ⟨h1,h2⟩:= hT
  obtain ⟨hq,hz⟩:= h2 Λ i p hJ hL (C.path.levels.blocks ..).branches rfl; let Y:= Ψ
  have hx:y=betaF G X (St).patch.L:= calendar_warm ..
  have ht:P.p.B=Perch.walls y:= hP.used ▸ rfl
  have hv:(Y).bp.B=Perch.walls X:= rfl
  have hp:Y.bp.threshold=temp (retime X):=h1.symm
  have h' : P.p.threshold=Paint.phase y := hP.used ▸ rfl
  have hs: i<N:= hi.trans_le hN; have hB:= (H.flash.clamp 0 (by decide) _ (O.court _ hl hi.le) _ (O.court (i+1) hf he) P.p Y.bp ht hv).upper.square
  have hm:= B.pays.stack N i p hs
  have hg:= bush_prices B J ξ O hP
  refine ⟨ships B N i p M hs,rfl,hP.exactTree.symm,hP.exactClip.symm,hp,H.yard i hl hi p,B.sized ..,
    ⟨B.world.H N (i+1),B.world.H N i,B.paths N _ hs _,B.paths N _ hs.le _,B.pays.crossings N i p hs,hm,⟨_,_,_,_,B.pays.all N _ hs _,B.pays.all N _ hs.le _⟩,B.sworn _ _ hs _,B.sworn _ _ hs.le _⟩,
    ⟨_,_,_,hP.rated,by rw [hL]; exact hq,hz⟩,hP.used ▸ rfl,⟨hv,hB⟩,?_,h'.trans (congr_arg _ hx)⟩
  rw [←hx]; exact hg

-- output record. Branch-specific scalar can use THIS serialization. Need equality on outputs ALL fields in Resin.
structure Theater (vP : Rep G (C.side (i+1) p)) (hV : Bush B J ξ (N:=N) H vP hi (hl.trans (Nat.le_succ i))) where
  commitment : Draft (tabloid B J ξ H hi hl (N:=N) vP) (tell B i) (retime X) l
  exhibit : Plate (tabloid B J ξ H hi hl vP (N:=N)) (retime X) l
  heated : 0<l
  positivity_ : 0<fiery G (retime X) (St).patch.L
  live : ∀ (Q : Rep G (C.side i p)) (hp : Q.p=(tabloid B J ξ H hi hl vP (N:=N)).bp) (hs : 25*radiusB (retime X)+30 ≤ Q.p.B),
     Opacity vP Q (fun j=> shiftZ (Orchard.canopy St) hp.symm (sprouting commitment exhibit (Orchard.canopy St) j)) (L:=foliage commitment) commitment.enrolled hs hV.rated
       ((tabloid B J ξ H hi hl vP (N:=N)).loading (retime X)) (J:=J) (D:= (tabloid B J ξ H hi hl vP (N:=N)).chi.profiles G St (retime X) l heated positivity_) (load ξ.era) (acres ξ X y) (Line ξ.era ξ.goal 0 s) (tinder ξ s)
include Z O M hN in
lemma intoProp : Nonempty (Theater B J ξ H hi hl P hP):=by
  let S':=C.path.levels.clock; let j:=S'.J k; let V:= initials (G:=G) B.prices S'.stage S'.kernel j j
  have hx : y=betaF G X (St).patch.L:= calendar_warm ..
  have hp := fitPost B M J ξ H Z O hN hi hl hP
  have hk: tell B i=V:=by unfold tell V S' j; rw [O.heft.plateau i hl hi.le, O.heft.plateau (i+1) (hl.trans (Nat.le_succ i)) hi]
  have ht := Z.great.localizes (St).patch (sizes_at ξ O hl hi p|>.2) (sizes_at ξ O hl hi p|>.1) (C.path.levels.blocks i p).branches; change Mesa J ξ V _ _ _ _ at ht
  rw [← hk] at ht
  obtain ⟨d,f,H,h,hz⟩:= ht.arrange (x:=X) (O.court i hl hi.le) St (Ψ) rfl rfl hp
  refine ⟨d,f,H,h,fun Q hQ hs=>?_⟩
  rw [show acres ξ X y=_ from congr_arg (acres ξ X) hx]; refine hz _ _ _ _ _ (show _ from hP.rated) Q hQ hs
-- Ticket is chosen AFTER caller P and H. Does not use guessed Rep Q.

structure Rewinds (z : Theater B J ξ H hi hl P hP) : Prop where
  reset :
    let Y:= tabloid B J ξ H hi hl (N:=N) P
    ∃ (Q : Rep G (C.side i p)),∃ hp:Q.p=Y.bp,
      Q.path=(C.path.rep N p i).path ∧ Q.clip=(C.path.levels.params i).clip ∧
      |P.beta-Q.beta|≤ (Υ).drift+ shear G ℓ ∧
      ThresholdE Q (C.path.levels.params i).width (C.path.levels.params i).paths (C.path.levels.clock.loopCap i) (C.path.levels.clock.allowance i) ∧
      ∀ hs : 25*radiusB (retime X)+30 ≤ Q.p.B,∃ α:Type, ∃ (_:Fintype α), ∃ (E : α→ Rim Q.p.threshold G (C.side i p)),
        let U := (fun j=> shiftZ (Orchard.canopy St) hp.symm (sprouting z.commitment z.exhibit (Orchard.canopy St) j))
        Resin P Q U (L:=foliage z.commitment) z.commitment.enrolled hs hP.rated (Y.loading (retime X)) E (load ξ.era) (kinetics s)



end YM.PhysicalNext.InteractingRank
