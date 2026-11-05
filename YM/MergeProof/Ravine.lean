import YM.MergeProof.Accord
import YM.MergeProof.Escarp
import YM.MergeProof.Gelatin

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
set_option quotPrecheck false
local notation "G'"=> Labels.frames G
include b hG
lemma ravine (h:Nest X Y) (N p m :ℕ)(hm:m<N) (d : ℕ)(hd:d+3 ≤ A.B.a.clock.J m){D:GaugeDoor ((H).rep N p (m+1)) ((H).rep N p m)}(hD:Climbs X Y N m p D)(hP:(1+2*(A.B.a.params m).columns)*Doors.rate (A.B.a.S.block m) ≤ Bid.barunit (A.B.a.S.block m)) : Relay.Tones (localSection G d) H N p (hol G) (waybill A.B.a m) m (Doors.rate (A.B.a.S.block m)) D:=by
    obtain ⟨l,v,Q,hT,x',hb,ht,hE⟩:= hD; subst D; have hK:= sound_duet H N p m hb ht (sandboxK hT x') (A.B.a.clock.op m p) (sounds hG hm hT x' b.r)
    let T:= A.B.a; let i:= T.clock.J m; let j:=T.clock.J (m+1); let c:= C j
    have hz:= step_paid A.B.a m; let V:= (H).rep N p (m+1)
    let Y':= Guard.Keeper.sufficient (h.samples hG N (m+1) p hm)
    let n:= (H).S.side (m+1) p; let A₀ := (0:Site n); let X₀ (i:{i : Support n// A₀∈i}): Wing:=.logKey (Blush.found A₀ i.val i.property)
    let Xk(q : StockTag n): Wing:= Wing.gasKey (cart Y' q)
    let V' := Set.range X₀ ∪ Set.range Xk; have hf: V'.Finite:= (Set.finite_range X₀).union (Set.finite_range Xk)
    obtain ⟨Vj,hV⟩:= clocksHere hm b.songs b.PStage b.wait (Graces.feet hd b.clock) h b.r hT x' hb ht hG b.tunes b.furthering b.corners b.shape b.clock b.stamp hd -- edit. namespace PriceCompiler?
    have hv := hV V' (fun i hi=> Or.inl ⟨⟨i,hi⟩,rfl⟩)
    have hE: waybill A.B.a m= 2*(Real.exp (V.p.supportExponent)* Cub.title G (M.p.profile j)):= by unfold waybill; rw [params_eq A.B.valid]; have he: V.p=A.B.a.budget (m+1):= Y.choice.represents N p (m+1) hm|>.vac; rw [he]
    rw [hE]; refine ⟨⟨hP,hK,mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Cub.title_one ..))),Doors.rate_pos _|>.le⟩,V',hf, fun U t hp hu ht' => asideP (localSection G d) H N p m (hol G) Y' U V' _ Y.choice hm hu ht' hp hK (Doors.rate_pos _|>.le) hv (glyphBound A.B.a (m+1)).2 (fun i=> Or.inr ⟨i,rfl⟩)⟩
end Bandage
end YM.PhysicalNext.Repeat.Legato
