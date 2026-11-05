import YM.FullVolume.Shroud.WAx
import YM.FullVolume.Shroud.Mass
/-! Ponds on every Cantata in orbit.Common.Volume.NT.Material halos never altered. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Accent
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Urns
open Pillars Bandage Pass Muse Contest Ovens
variable {R:Run G} {T:Campaign R} (W:Pillars R T)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
open Spirit Branch
variable {F:∀ p N,Contest N p T.L}(C:Cantata T F)
local notation "H"=> R.alloy.B.bake.make C.q
local notation "R₀"=> R.alloy
local notation "t"=> R.t
local notation "b₀"=> R.b
local notation "φ"=> far L!
local notation "w"=> near L!
local notation "ζ"=> fly L!
local notation "π"=> renal L!
local notation "M"=> mutt L! R.Q
def doorT (C:Cantata T F)(N p m:ℕ)(h:m<N):GaugeDoor ((R.alloy.B.bake.make C.q).rep N p (m+1)) ((R.alloy.B.bake.make C.q).rep N p m):= if he:1 ≤ m then ((C.mat N p).steps m he h).gate else ⟨0⟩
variable (S:Album T W C) (p N i:ℕ)
include W S
lemma ponds (h:1≤ i): Ponds (S.family T W C) R.w φ (waybill L!) w π ζ M (doorT C) p i N :=by
    let hG:= T.gains.SimpleR;let Z:= R.again hG|>.1.scrim; have hx := Z.costs; have hp:= R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books |>.1
    -- fixtures at each level.On any m≥i
    have hE(m): 100 ≤ (R.alloy.B.a.budget m).supportExponent:=by
       obtain ⟨v,y,h₁,h₂⟩:= hx.night.days (m+1) p m (by omega); exact h₂.exp.1
    have he:Retain (H) M π φ (doorT C) N p i:=by
       refine ⟨fun m hi hf=>?_,?_⟩
       · obtain ⟨U,hU⟩:= glassDoor hG R.b (q:=C.q) hf R.Q ((C.mat N p).steps m (h.trans hi) hf) hp.wall.hold (hp.wall.word _ _ (R.alloy.B.valid.pays m) _ (step_paid _ _)) (hE _) (hE _) -- result and
         unfold doorT; rw [dif_pos (h.trans hi)]; exact ⟨_,_,U,hU⟩
       exact hx.night.endow _
    have hF:= evaporates R.T (k:=i) hp.steps
    refine ⟨he,R.b.clock.room,R.b.clock.bank,⟨hF.water,hF.mint,hF.split,hF.support⟩,hx.mom,fun j hv hi=>?_⟩
    have hS:R.t j≤ i:=hv; have hl:= S.spent j N p (hS.trans hi); obtain ⟨T,hT,hR,hT'⟩:= hl
    obtain ⟨X,F,ht,hZ,hz,hq⟩:= hx.heights j i N p hS hi; refine ⟨⟨T,hR,hT'.1,?_,?_⟩,X,⟨F.coin,F.room,F.tap⟩,⟨ht.level,ht.cost⟩,⟨hZ.cost,hZ.candle⟩,hz,hq⟩
    · intro m hm hf; rw [doorT,dif_pos (show 1 ≤ m from (W.late j).trans hm)]; exact ((hT'.2 _ hm hf)).1
    intro v
    have hh:= rem_dominated (hT'.1.head.heard.earns v|>.2);
    change profile _ ((T.tone N).plays v).forced=hook _ _ (booster (localSection G j) _ 0 v); rw [hT] at hh ⊢
    exact onRise (localSection G j) (R.alloy.B.bake.make C.q) N p _ _ j v hh
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.ponds
