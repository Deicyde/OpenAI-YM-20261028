import YM.FullVolume.Rank.Mesa
/-! Payroll in the Banach notation. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open MergeProof MergeProof.Matric ConnectedActivityE6 Lim Neptune
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{S:Desk G n}{A:Hol G}{P:BudgetPoint}{ι κ:Type}
open Push.AbsoluteSums
namespace Rank
-- Pay not imposed when quoting available leads; wakes for true.
structure Shift (D:Desk G n) (f g:ℕ→Pin F n):Prop where
    charge :Tendsto (fun i=> (f i).1-(g i).1) atTop (𝓝 0)
    left : SeatE (fun i=> (f i).2.1) (fun i=> (g i).2.1) D.orient.p mapSeat
    right: Credit (fun i=>(f i).2.2) (fun i=>(g i).2.2)
set_option quotPrecheck false
variable {Y Z:ℕ→ Pin F n} (h:Shift S Y Z)
include h
local notation "R"=> S.orient
lemma trigger (v:ℝ)(hV:0<v):∀ᶠ n in atTop,(tell (Y n-Z n)).remBound 0 R S.k v:=by
   obtain ⟨s,hs,hS⟩:=h.left.vista.pay; obtain ⟨t,ht,hT⟩:= h.left.vests.pay; obtain ⟨a,ha,hA⟩:=h.right.left.use; obtain ⟨b,hb,hB⟩:=h.right.right.use
   let X i:=(mapSeat (n:=n) i); let E i k (p:ℝ): Prop:= S.orient.p.supBounds 0 (X k) (tell (Y i-Z i)|>.regular k) p; let K i k (p:ℝ):Prop:=0 ≤ p ∧ ∀ V, ‖(tell (Y i-Z i)).forced k V‖ ≤ p
   have he := curl (X:=X) S.orient.p (hs.tug ht) E (fun i k=> Next.Foundations.bound_sub (h.left.vista.reg ..) (h.left.vests.reg ..) (hS i k) (hT i k)) (fun i c he=> h.left.cost i c he) (v/2) (half_pos hV)
   let V i:= (S.orient.activities.forced i).support; have hq:= S.k; have hx:= curl (X:=V) S.orient.p (ha.tug hb) K (fun i k=> ⟨add_nonneg (ha.value ..) (hb.value ..),fun U=>(norm_sub_le ((Y i).2.2 k U) ((Z i).2.2 k U)).trans (add_le_add (hA ..) (hB ..))⟩) (fun i p hp=> (h.right.buys _ _ hp).mono fun n hn=> ⟨hp.le,hn⟩) (S.k*(v/2)) (mul_pos S.sane (half_pos hV))
   filter_upwards [he,hx] with i hi hk; obtain ⟨w,hw,-,hp⟩:=hi; obtain ⟨s,ht,-,hq⟩:= hk; exact ⟨_,_, (half_pos hV).le,(half_pos hV).le,(add_halves v).le,S.sane,⟨_,hp,hw⟩,_,hq,ht⟩
omit h
-- identity at same orientation independent. use phi.Log.K.
lemma same (P:Pin F n)(Y:Desk G n)(hv : ∃ v:ℝ, (tell P).remBound 0 Y.orient Y.k v)(hY:(tell P).Format 0 A Y.orient): Shift Y (fun _=>P) (fun _=>P) :=by
    obtain ⟨v,a,b,hp,hq,hv,hk,⟨f,hf,hS⟩,g,hg,hU⟩:=hv; let X i:=P.2.1 i; let Z i:= P.2.2 i
    have hs:SumE (fun _=>X) Y.orient.p mapSeat:=by
       have hx:= Sparse.constant (f:=f) (hf.2.1.of_nonneg_of_le (fun i=>(hS i).1) (fun i=>Y.orient.p.loMass _ _ (hS i).1)) (fun i=>(hS i).1); exact ⟨fun _ i=> hY.smooth _,_,hx,fun _ i=> hS _⟩
    have hb:Bill (fun _=> Z):= ⟨_,Sparse.constant (f:=g) (hg.2.1.of_nonneg_of_le (fun i=>(hU i).1) (fun i=>Y.orient.p.loMass _ _ (hU i).1)) (fun i=>(hU i).1),fun _ i V=> (hU _).2 V⟩
    refine ⟨by simp,⟨hs,hs,fun i p he=>?_⟩,hb,hb,fun i P=> by simp⟩
    simp only [sub_self]; exact Eventually.of_forall fun _=> bound_weaken ((regular0 ..).2) he.le
end Rank
end YM.FullVolume.Paint
