import YM.RG05Readout.Many.Release
import YM.RG05Readout.Many.View
import YM.MergeProof.South.Admit
/-!
# Per-step physical marked Census with alternatives

`Coursework` is for one REAL trajectory step. Carries exact polynomial density
already adjusted to singleton profiles; any number of independent slots over a
parent. Scale bookkeeping: choose ν=L^d per source, feed afterwards ν/t to
rename (usually t=card O). Restores χ only at compiler input check (action
always `HasSum` paid with direct transport and exact parent transmission).

Coalescing never powers or permutes occurrences. Even in aid computations on
full Bud used elsewhere, this proof keeps the polynomial of allowed sets with
all forced attributes as given by `Duty`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {n m p N:ℕ}{V W : Type}[DecidableEq V] [Fintype V][DecidableEq W][Fintype W] {R:Census V}{B:Census W}{a b c d t y z β:ℝ}
section
variable {n:Side}{Q:Rep G n}{F:Config G n →Poly R} {o:V→Site n}{w:V→ℝ}
    {P : V→Three G n}
structure MenuBoard (Q:Rep G n)(P:V→Three G n)(F: Config G n→ Poly R) (o:V→Site n)(w:V→ℝ)(d a:ℝ):Prop where
   cleared : Integrable F (prior G n)
   fettled i: Useful Q (P i)
   grants : Served Q (fun i=>(P i).2.1) (fun i=>profile Q.activities (P i).2.2) F o w d a
variable (h:MenuBoard Q P F o w d a)
include h in
lemma MenuBoard.check (hp:Q.activities.Valid Q.p b c)(U:Config G n):
    (F U).part R.quiet=Q.eval U∧∀ i,(F U).part (R.fire i)=(P i).1 U:=by
    obtain ⟨hA,hV⟩:=h.grants.relay (J:=R) (fun i=>(h.fettled i).normK) hp U
    exact ⟨hV,fun i=> (hA i).trans (congr_fun (h.fettled i|>.read) U)⟩

def combine {E:Type*}[AddCommGroup E][Module ℂ E] (δ:V→W)(a:V→ℂ)(p:V→E)(j:W):=∑ i:V, (if δ i=j then a i else 0) • p i

omit [Fintype V] [Fintype W] in
theorem feed_live {δ:V→W}(hv:License B R δ) (l:V→ℂ)(hc:Integrable F (prior G n)):Integrable (fun U=> feed l hv (F U)) (prior G n):= (((feed l hv).toLinearMap.toContinuousLinearMap).restrictScalars ℝ).integrable_comp hc
variable {δ:V→W} (l:V→ℂ) (hv:License B R δ) {q:W→Site n}{w':W→ℝ}
include h
lemma MenuBoard.blend (hr:Q.Lawful b c β y z)(ht:o=q ∘ δ)(hP:∀ i,w' (δ i)*‖l i‖ ≤ w i)(hp:∀ i,0<w i)(hW:∀ i,0<w' i) : MenuBoard Q (combine δ l P) (fun U=> feed l hv (F U)) q w' d a:=by
    let s (j:W)(i:V):= (if δ i=j then l i else 0); let X j i:= s j i • P i
    have hx(j i): Useful Q (X j i):=Useful.smul Q _ _ (h.fettled _)
    refine ⟨feed_live hv l h.cleared,fun j=> Useful.family Q hr Finset.univ (X j) (hx j),?_⟩
    have he:= carry_served hv l ht h.grants hP hp hW
    have hS : (fun i U=>∑ j, if δ j=i then l j* (P j).2.1 U else 0)=fun i=>(combine δ l P i).2.1:=by
       funext i U; rw [combine,Prod.snd_sum,Prod.fst_sum,Finset.sum_apply]; refine sum_congr rfl (fun j _=> ?_); split; rfl; change 0= (0:ℂ)* _; rw [zero_mul]
    have hg : (fun i p U=>∑ j, if δ j=i then l j* profile Q.activities (P j).2.2 p U else 0)=fun i=>profile Q.activities (combine δ l P i).2.2:=by
       funext i p U; unfold combine; rw [Prod.snd_sum,Prod.snd_sum,MergeProof.Float.prof_sum (fun j=> (X i j).2.2) (fun j=>(hx i j).normK), Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro j _
       change _= profile _ (s i j • (P j).2.2) _ _; rw [profile_scale]; unfold s; split; rfl; change _=(0:ℂ)*_; rw [zero_mul]
    rw [hS,hg] at he; exact he


lemma MenuBoard.same {P': V→Three G n} (hp:∀ i,Useful Q (P' i)) (hc:∀ i,(P i).2.1=(P' i).2.1)(hv:∀ i,profile Q.activities (P i).2.2=profile Q.activities (P' i).2.2): MenuBoard Q P' F o w d a:=⟨h.cleared,hp,by have H:=h.grants; simp_rw [hc,hv] at H;exact H⟩
end
section agenda
set_option quotPrecheck false
variable (A:History G)
variable {θ:Config G (A.S.side (m+1) p)→Poly R} {D: GaugeDoor (A.rep N p (m+1)) (A.rep N p m)} {l:V→ℝ}{r:ℕ→ℕ}
local notation "o1"=> A.S.side (m+1) p
local notation "o0"=> A.S.side m p
local notation "P"=> (A.rep N p m)
local notation "S"=> A.rep N p (m+1)
local notation "O"=> A.levels.clock.op m p
local notation "Ξ"=> (A.levels.budget m)
local notation "J'"=> (A.levels.budget (m+1))
local notation "X"=> (O).push (S).beta θ

structure Coursework (A:History G){N m p:ℕ}(r:ℕ→ℕ) (D: GaugeDoor (A.rep N p (m+1)) (A.rep N p m)) (d u t:ℝ):Prop where
    poses : Duty A r m d u t
    publishes : Volant (A.levels.clock.op m p) D (r m) ((A.levels.budget (m+1)).supportExponent-4) u ((A.levels.budget m).supportExponent+1/2) ((A.levels.budget m).supportExponent+1) 1 t
-- choose scaled ν list for stamps. usage through capture output may need PRECEDING projection; another proof.
variable {A} {I:V→Three G (A.S.side (m+1) p)}{J:V→Three G (A.S.side m p)} {o:V→Site (A.S.side (m+1) p)}{w:V→ℝ}{ν:V→ℂ}(he:Coursework A r D d b c)
local notation "T"=>fun i:V=>(ν i)⁻¹ • J i
include he
lemma Coursework.send (h :A.Selected) (hm:m<N)(hk:MenuBoard (S) I θ o w t 1)(hy:(J').supportExponent-4 ≤ t)
    (hC:∀ i,1 ≤ ‖ν i‖)(hp:∀ i,0<w i)(hL:∀ i, Ride (O) (o i) ((O).ratio.parent (o i)) D (ν i) (I i) (J i) (l i))
    (ho:Occupancy o (r m))(ho':Occupancy ((O).ratio.parent ∘ o) (r m)) (hm':∀ i,2*w i*l i≤1)
    {w':V→ℝ}(hv:∀ i,0<w' i)(hz:Repegs ((O).ratio.parent ∘ o) (Ξ).B (fun i=>d*w i) w' (1/2) 1 R):
    MenuBoard (P) T (X) ((O).ratio.parent ∘ o) w' (Ξ).supportExponent 1:=by
    let z:=A.levels.transition_mass m p ((S).beta); have hR(i): Ride (O) (o i) ((O).ratio.parent (o i)) D 1 (I i) (T i) (l i):=by
       have ht:= (hL i).matchPay 1 (ν i)⁻¹ 1 (show _=_ from by rw [inv_mul_cancel₀,one_mul]; exact norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hC i))); rw [one_smul,norm_one,norm_inv,max_eq_left (inv_le_one_of_one_le₀ (hC _)),one_mul] at ht; exact ht
    choose φ hφ y hy' hΦ using fun i=> (hR i).pays; let Y:= fun i=>(T i).snd.1; let Z:=fun i=>(T i).snd.2
    have hV(U i): (X U).part (R.fire i)=coin P (Y i) (Z i) U:=by
       have hF : (fun V=>(θ V).part (R.fire i))=(I i).fst:= funext fun V=>(hk.check (h.represents N p (m+1) hm).good.labels V).2 i
       have hO := push_get (φ:=θ) z hk.cleared (R.fire i); rw [hF,← one_smul ℂ ((O).push _ (I i).fst),← (hR i).exactStep,← (hR i).tomorrow.read] at hO; exact congr_fun hO U
    refine ⟨StepData.push_integrable z _ hk.cleared,fun i=>(hR i).tomorrow,Duty.pre A N m p r h hm he.poses he.publishes hp hv hk.grants hy ho ho' hz (F':=Y) (L':=Z) (fun i=> (hR i).tomorrow.normK) hV hm' ?_ (δ:=y) (r:=l) (fun i=>⟨φ i,hφ i,hΦ i⟩)⟩
    intro i; exact ((mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (hp i).le one_le_two) (hL i|>.nonneg))).trans (hm' i)
end agenda
end YM.RG05Readout.Many
