import YM.FullVolume.Dusk.Noa
import YM.FullVolume.Dusk.Cargo
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
variable {R:Run G} (T:Campaign R)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
local notation "o"=> R.alloy.B.a.clock.bar
open Spirit Branch
open Boutique
-- **pack all given at their diagonals independently**, ghosts not coupled at m=0 because not observed ever. Use spirit for q and branch copying from any Albums with same incoming at levels ≥1.Fproof.
variable (Φ':∀ p N, Contest N p T.L)(hp:∀ p N, |(Φ' p N).bonusB - R.alloy.B.a.clock.bar| ≤ outing T p)
local notation "s"=> spirit T Φ'
variable {Q : ℕ→ℕ→∀ p N, Contest N p T.L}(C : ∀ p i, Cantata T (Q p i))(he : ∀ p N, Φ' p N=Q p N p N)
include hp he
lemma packs : ∃ A:Cantata T Φ',∀ p N,Courant ((C p N).mat N p) (A.mat N p):=by
   let S:= spirit T Φ'; have ha:= bornMeet T Φ' hp
   have hz p N i (h:1 ≤ i)(hi:i≤N): S N p i= (Φ' p N).trail i:= at_height T Φ' (h.trans hi) i h
   have hf N p i (h:1 ≤ i)(hi:i≤N): (C p N).q N p i=S N p i:=by rw [hz _ _ i h hi,he]; exact (C p N).palm N p (h.trans hi) i h hi
   have hP N p:∃ P:Branch R.kit S N p 1,Courant ((C p N).mat N p) P ∧ ∀ m,∀ h:1 ≤ m,∀ hm:m<N,Flavor T.L (P.steps m h hm):=by
       let Y:= C p N; let X:= Y.mat N p
       have hw i (h:1 ≤ i)(ht:i<N):∃ U:Boutique R.kit S N p i,Flavor T.L U ∧ Stitch (X.steps i h ht) U:= Boutique.fashioned _ (hf N p _ (h.trans i.le_succ) ht) (hf N p _ h ht.le) (Y.links ..)
       choose M H H' using hw
       let P: Branch R.kit S N p 1:=⟨ha,fun i h hi=> (show (K!|>.bake.make Y.q).rep N p i=(K!|>.bake.make S).rep N p i from hf N p i h hi) ▸ X.slots i h hi,M⟩
       exact ⟨P,⟨hf N p,H'⟩,H⟩
   choose F H hF using hP
   exact ⟨⟨S,F,fun N p h i=> hz p N i,hF,fun p=>congr_fun (fades T Φ') p⟩,fun p N=> H N p⟩
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.packs
