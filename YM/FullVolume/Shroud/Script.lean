import YM.FullVolume.Shroud.Vigil
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
variable (F:∀ p N, Contest N p T.L)(hp:∀ p N, |(F p N).bonusB - R.alloy.B.a.clock.bar| ≤ outing T p)
section ready
lemma sturdy (p N:ℕ)(m:ℕ)(h:m ≤ N) : let Y:= F p N|>.trail m; HasSlots Y.p Y.activities:=by
    intro S; let P:=F p N; have hg:= P.rises
    have hp:= T.L.disappears hg; rcases eq_or_lt_of_le h with h|h
    · subst m; exact hp.fromTop.inits.2
    obtain ⟨l,t,Q,hT,x,hx,hQ,hK⟩:= (hp.persists m (Nat.zero_le _) h).continues.2.1
    let g:=T.gains.SimpleR; have hk:S=hT.result x:= hK
    rw [hk,hT.owns g h hx]; have hb:= hT.core h x hx; have hp:= (R.kit.machine.passes h hT.knows).1
    exact (hb.renew g (R.alloy.B.support.cap N m h.le) hp.decent hp.width _ (Return.enough_room ..) (hp.fees x hx)).spare_room ..
structure Cantata (F : ∀ p N,Contest N p T.L) where
    q:ℕ→∀ p, Shoot.Trail L! p
    mat : ∀ N p, Branch R.kit q N p 1
    palm : ∀ N p:ℕ,∀ h:1 ≤ N,∀ m:ℕ,1 ≤ m → m ≤ N → q N p m= (F p N).trail m
    links : ∀ N p m,∀ h:1 ≤ m,∀ hm:m<N,Boutique.Flavor T.L ((mat N p).steps m h hm)
    zero : ∀ p,q 0 p=R.T.history 0 p
include hp
lemma cant : Nonempty (Cantata T F):=by
    let s:= spirit T F; let H:= (R.alloy.B.bake.make s); have hv N p m (h:1 ≤ m)(hf:m≤N): s N p m= (F p N).trail m:= at_height T F (h.trans hf) m h
    have he N p m (h:1 ≤ m)(hf:m≤ N): HasSlots (H.rep N p m).p (H.rep N p m).activities:=by change HasSlots (s N p m).p (s N p m).activities; rw [hv _ _ m h hf]; exact sturdy T F p N m hf
    have hp' N p m (h:1 ≤ m)(hf:m<N):∃ Q:Boutique R.kit s N p m,Boutique.Flavor T.L Q:=by
       let P:= F p N; have hl:= P.rises.prices (m+1) (Nat.zero_le _) hf
       apply Boutique.brands (F₀:=T.L) hf _ _ (he N p m h hf.le) (he N p (m+1) (h.trans m.le_succ) hf)
       · change (T.L.prim N m p hf).sails (s N p m) (s N p (m+1)); rw [hv _ _ _ h hf.le,hv _ _ _ (h.trans m.le_succ) hf]; exact P.twines m hf
       change Lives (R.alloy.B.bake) N _ p (s N p (m+1)) ∧ (s N p (m+1)).beta∈_; rw [hv _ _ _ (h.trans m.le_succ) hf]; exact ⟨T.L.altitude.1 hl.1,hl.2⟩
    choose B hB using hp'; exact ⟨s,fun N p=> ⟨bornMeet T F hp,he N p,B N p⟩,fun N p _ m=> hv N p m,hB,fun p=> congr_fun (fades T F) p⟩ -- congr_fun binder
end ready
variable (C:Pillars R T)
lemma strength :∃ S':Cantata T (fun p N=> T.center N p), S'.q=R.T.history ∧ (∀ m p n,∀ h:1 ≤ m,∀ hv:m<n, HEq ((S'.mat n p).steps m h hv) ((C.yields n p).steps m (Nat.zero_le m) hv)):=by
    refine ⟨⟨R.T.history,fun n p=>⟨R.T.choice,fun i _ hi=> (C.yields n p).slots i (Nat.zero_le _) hi,fun i _ he=> (C.yields n p).steps i (Nat.zero_le _) he⟩,fun _ _ _ _ _ _=>rfl,fun _ _ _ _ _=> C.shares ..,fun _=>rfl⟩,rfl,fun _ _ _ _ _=> HEq.rfl⟩
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.cant
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.strength
