import YM.FullVolume.Shroud.Script
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
open YM.MergeProof
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp
open Pillars Bandage Pass Muse Contest Ovens
variable {R:Run G} (T:Campaign R) (W:Pillars R T)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
local notation "o"=> R.alloy.B.a.clock.bar
open Spirit Branch
variable {F:∀ p N, Contest N p T.L} (C:Cantata T F)
open Boutique
section
local notation "H"=> R.alloy.B.bake.make C.q
local notation "p₀"=> fun i=> Boutique.attire R.T i
-- Petra.Totus.Field Ledger.What about Sensor.Bold.Time.
-- Keep output Choice.Frame. Reading values.Authentic R'.history from trials on upper portion.
structure Album where
    record :∀ d N p, TransferData ((Labels.frames G).level d) (R.alloy.B.bake.make C.q) N p
    spent : ∀ d N p, ∀ h:R.t d ≤ N,Piano R.b (C.mat N p) (fun i=> brochure R.T i p R.tuning.receipts) (W.late d) (R.accepts d) (record d N p) h
    priced : ∀ d N p,R.t d ≤ N → (record d N p).Based (hol G) (localSection G d) (R.t d)
include C
lemma hasRecord : Nonempty (Album T W C):=by
    let h:=T.gains.SimpleR; let hz:=R.tuning.receipts
    have hf(d N p):∃ V:TransferData ((Labels.frames G).level d) (H) N p,∀ h':R.t d ≤ N,V.Based (hol G) (localSection G d) (R.t d) ∧ Piano R.b (C.mat N p) (fun i=> brochure R.T i p hz) (W.late d) (R.accepts d) V h':=by
       by_cases hQ:R.t d ≤ N
       · obtain ⟨V,hV⟩:= (C.mat N p|>.composing h R.b hz (fun i=> brochure R.T i p hz) (W.late d) (R.accepts d) hQ); exact ⟨V,fun _=> hV⟩
       exact ⟨⟨fun _ v=>Extra.Histories.primary 0 v,LinearEquiv.refl _ _⟩,fun h=>False.elim (hQ h)⟩
    choose S hS using hf; exact ⟨S,fun d N p hi=> (hS d N p hi).2,fun d N p hi=> (hS d N p hi).1⟩
namespace Album
variable (P: Album T W C)
def family:= Family.mk (H) (hol G) (Labels.frames G) (localSection G) R.t P.record
abbrev makeFamily := P.family T W C
-- no claim calibrated Spec below Reference.L.Directional.Drift.U.
include P
lemma makes : P.family T W C |>.Makes:=by
    let b:=R.b; let ha:= Issue.refer H R.w R.y R.t b.clock R.accepts
    exact ⟨(C.mat 0 0).choice, ha.gets, ha.order,ha.fits, fun d N p hi x v=> ha.loaded d N hi _ rfl rfl _ x v,P.priced⟩
end Album
end
section stamp
-- retrieval center, not via equality of stories.P.App.
local notation "H"=> R.alloy.B.bake.make R.T.history
local notation "centerF"=> fun p N=> T.center N p
noncomputable def visible : Cantata T centerF:= ⟨R.T.history,fun n p=>⟨R.T.choice,fun i _ hi=> (W.yields n p).slots i (Nat.zero_le _) hi,fun i _ hi=> (W.yields n p).steps i (Nat.zero_le _) hi⟩,fun _ _ _ _ _ _=>rfl,fun _ _ _ _ _=> W.shares ..,fun _=>rfl⟩
def stamped : Album T W (visible T W) where
   record:= R.stories
   spent := by
     intro d N p h
     obtain ⟨Z,hP,hR,hT⟩:= W.ports d N p h
     exact ⟨Z,hP,hR,hT⟩
   priced d N p h:= R.makes.calibrated d N p h
lemma billbook : Album.family T W (visible T W) (stamped T W)= R.family:=rfl
end stamp
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.hasRecord
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.billbook
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Album.makes
