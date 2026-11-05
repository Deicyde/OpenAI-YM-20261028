import YM.TraceExtension.Perfect.Liturgy
import YM.Planned.PRIMARY_INTEGRAL_295.Edens
import YM.Work.F04
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG RG.Supply Wilson Finset Push.Uniform Planned.PrimaryIntegral295 Next.Free Org Input Extra.Histories
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{M:Metals G}{D:Rolls M.p}{A: Alloy M D}
private lemma path_actual (Z:Bolt A)(N i p:ℕ)(h:i ≤ N): A.B.kin.path N i=((Issue.trail Z).rep N p i).path:=by
 have hx:= ((Z.sticks N p).prices i (Nat.zero_le _) h).1.path; rw [A.B.bases] at hx; exact hx.symm
set_option quotPrecheck false
local notation "p!"=>A.B.a.clock
section
variable (B:Bolt A)(N p m:ℕ)(hk:m+1<N) (E:Ember A.B.a m)
local notation "ω!"=> (Issue.trail B).levels
local notation "R"=> A.B.kin
local notation "V"=> A.B.M
local notation "K"=> A.B.a.clock.op m p
local notation "f!"=> A.B.a.S.side (m+1) p
local notation "mot"=> (A.post).η (A.B.a.clock.J (m+1))
-- custom support
include hk
private lemma vote : Bid.Sworn ((V).H N (m+1)) (A.B.a.S.side (m+1) p) G := (Edens.laureates A.B.a V A.B.plan N (m+1) p hk).2.2
include E
local notation "E!"=> Carrier.linesOf (destination A.B.a N m) A.B.a.clock.kernel.penalty
private lemma trials (F:Forest (K).ratio): Guessed F (installed (K).ratio E!) ((R).stationary N m p F):=by
 have hi:= A.B.support.critical N m p (by omega) F; have hp:= A.B.plan.all N (m+1) hk.le ((A.B.a.S.side (m+1) p)); let Z:=K
 obtain ⟨ho,hw⟩:=hi
 have hm:= A.B.support.cap N (m+1) hk.le
 let c:=A.B.a.params (m+1); let C:= A.B.kin.path N (m+1)
 have hx:= (Work.F03.answer G _ _ Z (bigger m E p) F ((V).H N (m+1)) c.clip C c.width c.paths _ _ _ hp hm (A.B.support.links N (m+1) hk.le) (vote N p m hk) (Work.F02.answer _ _ _ _ _ _ hm)).2
 have hv: Inputs Z (installed (Z.ratio) E!) (((V).H N (m+1)).metric.acts _) (((V).H N m).metric.acts _):= (Edens.laureates A.B.a V A.B.plan N m p (by omega)).2.1.trial
 intro x; let t:Z.Choices:= Classical.arbitrary _
 have hT:= Work.F04.tangent F c.clip C mot (A.post.price _) (A.B.support.gap N m p (by omega) F) ((V).H N (m+1)) ((V).H N m) (installed Z.ratio E!) hv hx _ ho t x
 change HasDerivAt _ (relative F (installed Z.ratio E!) x) _; rw [← hT]
 exact Push.side _ (ho.2.1.differentiableAt (by simp)) _
local notation "P!"=> (A.B.a.clock.op m 0).patch
local notation "S!"=> (A.B.a.params (m+1))

def native : Slide G ((A.B.a.clock.op m 0).patch) A.B.a.clock.kernel (A.B.a.params (m+1)).clip (A.B.a.params (m+1)).width (A.B.a.params (m+1)).paths E.α E.B:=by
 let Y:= Classical.choice (Tree.select (K).ratio (K).patch.odd_side); let r:= (R).stationary N m p Y; have hp:= A.B.support.critical N m p (by omega) Y
 exact {
    c:= A.B.a.S.side m p
    f:= f!
    s:= K
    kit:= rfl
    patch:=rfl
    wood:=Y
    b:= A.B.kin.path N (m+1)
    Λ:=A.B.a.clock.loopCap (m+1)
    ρ:=r
    law:=hp.1
    price:= A.B.support.cap N (m+1) hk.le
    size:=bigger m E p
    k:= E!
    t:=Classical.arbitrary _
    shade:= fun l hx=> E.bill (destination A.B.a N m) l (by have hp:=E.smooth; omega)
    color:= Ether.witty (destination A.B.a N m) _ A.B.a.clock.kernel.penalty_pos E.legal
    guage:=trials N p m hk E Y }
end

section
variable (B:Bolt A) {W:Type}(N p: W→ℕ)(m:ℕ)(Z:Filter W)(hk:∀ w,m+1<N w)(E: Ember A.B.a m)(he:Tendsto (fun w=> (A.B.a.S.side m (p w)).val) Z atTop)
-- transition to SAME lower Period
local notation "f!"=> fun w=>(A.B.a.S.side (m+1) (p w))
local notation "c!"=> fun w=> A.B.a.S.side m (p w)
local notation "o!"=> fun w=> native (N w) (p w) m (hk w) E
local notation "R"=> A.B.kin
local notation "e!"=> A.B.a.clock.hatBeta
local notation "P"=> (A.B.a.clock.op m 0).patch
include he
lemma paid_native : LotFee Z (fun w=>native (N w) (p w) m (hk w) E) (east (A.B.a.clock.hatBeta m)) (east (A.B.a.clock.hatBeta (m+1))) E.H E.D:=by
 obtain ⟨hx,hz,C,D,H,h⟩:= E.status
 refine ⟨he,?_,E.sA,E.sB, inv_pos.mpr (Real.log_pos hx),inv_pos.mpr (Real.log_pos hz), h,E.shoe,E.fit,H,D⟩
 refine he.eventually (eventually_ge_atTop (max (8*((P).L.val+1)+4) 11)) |>.mono (fun w hv=> ?_)
 exact Nat.le_trans hv (Nat.mul_le_mul_left (A.B.a.S.period (p w)).val (A.B.a.S.den_strict.monotone (Nat.le_succ m)))
variable {K:∀ w:W,Dart G (A.B.a.S.side (m+1) (p w))} (ht:∀ w:W,(K w).Sound (A.B.kin.path (N w) (m+1)) (A.B.a.params (m+1)).clip) (j:ℕ) (h:Saving Z K (east (A.B.a.clock.hatBeta (m+1))) (reed (A.B.a.clock.hatBeta (m+1))) (vista j (A.B.a.clock.hatBeta (m+1))))
local notation "k!" => fun w=>Dart.down (o! w).wood (o! w).ρ (K w) (o! w).t (P).L
include h ht hk E
set_option maxHeartbeats 400000 in
lemma pay_step : ∃ M:∀ w,Dart G (A.B.a.S.side m (p w)),(∀ w,(M w).Sound (A.B.kin.path (N w) m) (A.B.a.params m).clip) ∧ Saving Z M (east (A.B.a.clock.hatBeta m)) (reed (A.B.a.clock.hatBeta m)) (vista (j+1) (A.B.a.clock.hatBeta m)):=by
 let X:=fun w=>native (N w) (p w) m (hk w) E
 let M:=fun w:W=>(K w).down (X w).wood (X w).ρ (X w).t (P).L
 have hz(w:W): (K w).Sound (X w).b (A.B.a.params (m+1)).clip:= ht w
 have hi(w): m < N w := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (hk w).le
 refine ⟨M,fun w=> ?_,save_step (X:=X) (K:=fun w=>K w) hz (paid_native N p m Z hk E he) h (E.bank j) E.pays E.status.2.2.1⟩
 apply Dart.Sound.balance (T:=(X w).s) (X w).t (P).L rfl (X w).law (X w).price (X w).size.1 (A.B.support.gap (N w) m (p w) (hi w) (X w).wood) (A.post.price _) (hz w) (A.B.support.classicalPart (N w) m (p w) (hi w) (X w).wood) (A.B.support.cap (N w) m (hi w).le)
end
end YM.Trace.Perfect
#print axioms YM.Trace.Perfect.pay_step
