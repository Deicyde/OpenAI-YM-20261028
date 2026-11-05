import YM.MergeProof.Escarp
import YM.OPE.Columns.Accounts
import YM.OPE.Columns.Clock

/-!
# Keep uniform leading heading alongside our Music witnesses

Strengthening of YM/MergeProof/Escarp.lean; most of the proof is
the *same* construction. Adapted from that file, retaining the baseline.
-/
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
-- keep chosen Sage. Different d reuse. Legato.
include b hG
lemma chorus_columns (h:Nest X Y) (N p m :ℕ)(hm:m<N): ∃ D:GaugeDoor ((H).rep N p (m+1)) ((H).rep N p m), Climbs X Y N m p D ∧ ∀ d:ℕ, d+3 ≤ A.B.a.clock.J m → TuneColumns (localSection G d) H N p (hol G) K m D (waybill A.B.a m):=by
    obtain ⟨l,v,Q,hT,x,hx,hQ,hz⟩:= (h.held N m p hm).1
    let x' : Set.Icc l v:=⟨x,hx⟩; have hb: (H).rep N p m=hT.result x':=hz; have ht:(H).rep N p (m+1)=Q x':=hQ
    let D:= duet _ _ _ _ hb ht (sandboxK hT x'); refine ⟨D,⟨l,v,Q,hT,x',hb,ht,rfl⟩,fun d hd=>?_⟩
    let T:= A.B.a; let i:= T.clock.J m; let j:=T.clock.J (m+1); let c:= C j
    have hz:= step_paid A.B.a m; let V:= (H).rep N p (m+1)
    let Y':= Guard.Keeper.sufficient (h.samples hG N (m+1) p hm)
    let n:= (H).S.side (m+1) p; let A₀ := (0:Site n); let X₀ (i:{i : Support n// A₀∈i}): Wing:=.logKey (Blush.found A₀ i.val i.property)
    let Xk(q : StockTag n): Wing:= Wing.gasKey (cart Y' q)
    let V' := Set.range X₀ ∪ Set.range Xk; have hf: V'.Finite:= (Set.finite_range X₀).union (Set.finite_range Xk)
    obtain ⟨Vj,hV_ope,hV⟩:= clocksHere_columns hm b.songs b.PStage b.wait (Graces.feet hd b.clock) h b.r hT x' hb ht hG b.tunes b.furthering b.corners b.shape b.clock b.stamp hd -- edit. namespace PriceCompiler?
    have hv := hV V' (fun i hi=> Or.inl ⟨⟨i,hi⟩,rfl⟩)
    have hE: waybill A.B.a m= 2*(Real.exp (V.p.supportExponent)* Cub.title G (M.p.profile j)):= by unfold waybill; rw [params_eq A.B.valid]; have he: V.p=A.B.a.budget (m+1):= Y.choice.represents N p (m+1) hm|>.vac; rw [he]
    rw [hE]; refine ⟨⟨V',hf,Y',fun i=> Or.inr ⟨i,rfl⟩,Vj,c,_,hv,b.clock.fits H rfl m d (by have hδ:=hd; omega),hV_ope⟩, sound_duet H N p m hb ht (sandboxK hT x') _ (sounds hG hm hT x' b.r),?_,(glyphBound A.B.a (m+1)).2⟩
    apply mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Cub.title_one ..)))
end Bandage
end YM.PhysicalNext.Repeat.Legato
