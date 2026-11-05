import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Unlid
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Endow
import YM.TraceExtension.Prom.Port.Leashes
import YM.TraceExtension.Prom.Port.Opacity.Forestage
import YM.TraceExtension.Prom.Port.Pleas
import YM.TraceExtension.Prom.Port.Soft.Bonfire
import YM.TraceExtension.Prom.Port.Soft.Postsale
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Unlid for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Glyph Thirst Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
     YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory Bid Function Display Display.Docking Display.Sew Tree Pump Atlas Next.Rank.Station Vale
open scoped Topology BigOperators Classical
variable {G : Gauge}
section fire
variable {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S}
    {P : Teller G} {W ι κ α : Type} [Fintype W] [DecidableEq W] [Fintype ι] [Fintype α]
    {u : W → Site c}
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (A : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B)
    {o ℓ δ Λ η M l σ e y w v : ℝ} (hR : (white R).Lawful o ℓ Λ δ η)
    {ν : Config G c→ℝ} {D : Allocation G S x w} {J : ChartRatio G}
    (E : α→ Rim R'.p.threshold G c)
    (he : Veins (white R) R' p A hs hR e M l σ) (hv : BodyGrant T R L D J R'.p.threshold p (fun V=> ((ν V:ℝ):ℂ)))
    (Ly : Lease S.patch.L R.p R'.p e M l σ y η)
    (hp : Resin (white R) R' p A hs hR ν E e y)

include Ly hp he hv
-- stage-1 Plough fireplace proof at P0

end fire
variable {C : Family G} {N k p i : ℕ} {w r l a : ℝ}
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
local notation "D" => kinetics (Atlas.clim C.path.levels k)
variable (H : ShowHoursSky J B ξ k w l r) (Z : VentsSky B ξ J l r k) (O : CorridorSky C.path.levels ξ.band ξ k) (hN : k ≤ N)
section lift
variable {P : Rep G (C.side (i+1) p)} (hi : i<k)(hl : Station.widthSky C.path.levels ξ.band k ≤ i) (hP : BuoyantSky B J ξ (N:=N) H P hi (hl.trans (Nat.le_succ i)))
structure AriseSky (P : Rep G (C.side (i+1) p)) (Q : Rep G (C.side i p)) : Prop where
  lesions : BuoyantSky B J ξ (N:=N) H Q hi.le hl
  still : P.beta=Q.beta
  pushes : Q.eval=(C.path.levels.clock.op i p).push P.beta P.eval
  heats : ∃ h:25*radiusB (retime X)+30≤ Q.p.B,∃ B':Boosted t (tell B i) (retime X),∃ (L:Lantern G St) (D' : Allocation G St (retime X) l), Coupler (t) L J D' P.beta ∧
    ∀ u:ℝ, u>0→Kiln P Q B' h J L D' u (load ξ.era) ((gas ξ.era.coast X^2)⁻¹) (Line ξ.era ξ.goal 0 s) (D/16) (D/4) D ∧
      Kiln P Q B' h J L D' u ξ.era.coast.e (gas ξ.era.coast y)⁻¹ 1 (D/16) (D/4) D
-- weaken white from E=0 only; never summon E at Calendar allowance along this stretch for truly applied P
private lemma buoySky (Q : Rep G (C.side i p)) (hβ : P.beta=Q.beta) (hq : Q.p= Paint.inbox C i (H.oldPrices i hi.le hl))
    (h₁ : Q.path=(C.path.rep N p i).path) (hC : Q.clip=(C.path.levels.params i).clip)
    (he : Tissue Q (C.path.levels.params i).width (C.path.levels.params i).paths (C.path.levels.clock.loopCap i) (rollup s (k-i)) (gas ξ.era.coast X))
    (_ : CorridorSky C.path.levels ξ.band ξ k)
    (_ : BuoyantSky B J ξ (N:=N) H P hi (hl.trans (Nat.le_succ i))): BuoyantSky B J ξ (N:=N) H Q hi.le hl:=by
  rename_i O ht
  have hh:0 ≤ C.path.levels.clock.allowance i:= by unfold Calendar.allowance Calendar.hatCoupling; positivity
  obtain ⟨p,⟨h,h₂,hM,⟨z,hz,hP⟩,hH⟩⟩:= he.status
  refine ⟨⟨hq,h₁,hC,?_,⟨p,h,h₂,hM,⟨z,hz,fun i=>⟨(hP i).1,(hP i).2.1,(hP i).2.2.trans hh⟩⟩,hH⟩⟩,he⟩
  change |Q.beta-s| ≤ s/8; rw [← hβ]; exact ht.warm.βgap
include M O hP hN Z
lemma arousingSky (hb: 0≤ ξ.band) : ∃ Q,AriseSky B J ξ H hi hl (N:=N) P Q:=by
  obtain ⟨T⟩:= liftedSky B M J ξ H Z O hN hi hl hP hb
  obtain ⟨Q,h⟩:= furySky B M J ξ H Z O hN hi hl hP T hb
  obtain ⟨hS,hL⟩:= coast_leaseSky B J ξ H hi hl hP.warm O Q h.params
  obtain ⟨e,-,hX,hB⟩:= elongationSky B J ξ Z O hi hl (p:=p)
  have hF:Lease (St).patch.L (white P).p Q.p (load ξ.era) (acres ξ X y) (Line ξ.era ξ.goal 0 s) (sailboat s (k-(i+1))) (kinetics s) (gas ξ.era.coast y):=
    hX.books (k-(i+1)) X y _ _ ((Nat.sub_le_sub_left (Nat.le_succ _) _).trans hB) (O.court _ hl hi.le) (O.court _ (hl.trans (Nat.le_succ i)) hi) (h.params ▸ rfl) hL
  obtain ⟨hT,hY⟩:= T.paid Q h.params hS
  obtain ⟨n,hN⟩:= holding_graphSky B M J ξ H hi hl hP.warm O hN
  have hU:=h.funds hS
  let L:= foliage T.commitment; let v:Dyed G St:= tabloidSky B J ξ H hi hl P (N:=N)
  let N':= v.chi.profiles G St (retime X) l T.heated T.lives
  have hv: Coupler (t) L J N' P.beta:= hN _ rfl _
  have hY' := churning _ _ _ _ _ _ _ hT hF hU (acres_pay ξ X y) h.hm h.hk h.pets
  let z:= germinates (L:=L) (white P) Q (fun j=> shiftZ (Orchard.canopy St) h.params.symm (sprouting T.commitment T.exhibit (Orchard.canopy St) j)) T.commitment.enrolled hS hP.pets.status (Empty.elim : Empty→Rim Q.p.threshold G (C.side i p))
  refine ⟨z,⟨buoySky B J ξ H hi hl z h.beta.symm h.params h.tree h.clip hY' O hP,h.beta.symm,?_ ,hS,T.commitment.enrolled,L,N',hv,fun u hu=>⟨?_,?_⟩⟩⟩
  · exact made_soft P _ _ _ hS hP.pets _ hT (show Lease _ P.p _ _ _ _ _ _ _ from hF) (show BodyGrant (t) P L N' _ _ _ _ from hY) hv _ hU hY'
  · exact stove P Q _ _ _ _ _ hT hY hF hU le_rfl (le_max_left ..) le_rfl hu
  exact stove P Q _ _ _ _ _ hT hY hF hU (show ξ.era.coast.e≤load ξ.era by unfold load; linarith only) (le_max_right ..) (le_max_left 1 _) hu
end lift
end YM.PhysicalNext.InteractingRank.Soft
