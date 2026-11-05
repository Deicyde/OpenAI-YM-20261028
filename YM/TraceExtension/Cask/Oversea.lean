import YM.TraceExtension.Cask.Common
import YM.MergeProof.South.Block
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open GridApprox Local Extra.Trajectories Source Extra.Multi Accent Menu Overlay
open scoped Classical
variable {V:Type}[DecidableEq V]{G:Gauge}[Fintype V]{B:Census V}
variable {H:History G}{r:ℕ→ℕ}{δ u:ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
set_option quotPrecheck false
variable (hw:H.Selected) (hx:Moonlit H r δ u D) {p N k m:ℕ}{o:∀ i:ℕ,V → Site (H.S.side i p)}{w:ℕ→V→ℝ}
local notation "R"=> H.rep N p
local notation "A"=> H.levels
local notation "P"=> H.levels.budget
local notation "a"=> (fun i=>(H.levels.budget i).supportExponent)
local notation "n!"=> H.S.side k p
variable {X:Config G (H.S.side k p)→ Poly B}
lemma quietV {n:Side}{Rt: Activities G n}: profile Rt 0=0:=by ext i U; all_goals simp only[profile,cram,Pi.zero_apply,tsum_zero]
lemma mellow {n:Side}{Rt:Rep G n}: coin Rt 0 0=0:=by ext U; all_goals simp [coin,nickel]
include hx hw
lemma floor_s (h:m<k)(hk:k ≤ N)(hB:Matchup H r δ p k m o w B)(hf:Served (R k) 0 0 X (o k) (w k) (a k-4) 1) (he:Integrable X (prior G _)): Served (R m) 0 0 (gust H N p k X m h.le) (o m) (w m) (a m) 1 :=by
   let ϕ i := if i=k then a i-4 else a i; let v i h:= gust H N p k X i h
   suffices hh : ∀ i:ℕ,m ≤ i→∀ h':i≤k, Served (R i) 0 0 (v i h') (o i) (w i) (ϕ i) 1 by
     rw [← (if_neg h.ne:ϕ m=a m)]; exact hh m le_rfl h.le
   intro i hi hk'; induction hk' using Nat.decreasingInduction with
   | self=> rw [show v _ _=X from gust_base ..,show ϕ k=_ from (if_pos rfl : ϕ k=a k-4)]; exact hf
   | of_succ i he' IH=>
      let q:= v (i+1) he'; let Z:= H.levels.clock.op i p; let W:= Z.push (H.β N p (i+1)) q; have hi' : m ≤ i+1:= hi.trans i.le_succ
      have hp: Served (R (i+1)) 0 0 q (o (i+1)) (w (i+1)) (ϕ (i+1)) 1:= IH hi'; obtain ⟨s,z,hu,hr⟩:= hx.days N p i (he'.trans_le hk)
      let g(j):ℕ → Config G (H.S.side j p)→ℂ:= 0; have hq(j): Dominated (g j):=by refine ⟨fun _=>0,summable_zero,fun i U=>?_⟩; simp [g]
      have ht (j): (fun _ : V=>profile (R j).activities (g j))=0:= by simp_rw [g,quietV];rfl
      have hψ : ϕ i=a i:= if_neg he'.ne; rw [hψ]; let p':=Z.ratio.parent ∘ o (i+1); have hx:p'=o i:= hB.pins i hi he'; have hs : v i he'.le=W:=gust_step ..
      have hZ j s : coin (R j) 0 (g j) s=0:=congr_fun mellow _; have hh(t U): (W U).part (B.fire t)=coin (R i) 0 (g i) U:=by
         have heq : (fun U=> (q U).part (B.fire t))=0:=funext (fun U=> (Served.relay (show Served (R (i+1)) (fun _=> (0:Config G _→ℂ)) (fun _=> profile (R (i+1)).activities (g (i+1))) q _ _ _ 1 from by rw [ht]; exact hp) (fun _=>hq _) (hw.represents N p _ (he'.trans_le hk)|>.good.labels) U|>.1 t).trans (hZ _ _)); rw [show (W U).part (B.fire t)= _ from congr_fun (push_get (H.levels.transition_mass ..) (gust_live H N p k X he he') (B.fire t)) U,hZ]; change Z.push _ _ U= _; rw [heq]; simp [StepData.push]
      have hv: a (i+1)-4 ≤ ϕ (i+1):= by unfold ϕ; split;exact le_rfl; linarith only
      rw [hs, ← hx, ← ht i]; refine Duty.pre H N i p r hw (he'.trans_le hk) hr hu (hB.pos _ hi' he') (hB.pos _ hi he'.le) hp hv (hB.next _ hi he') (show Occupancy p' _ from by rw[hx];exact hB.occ _ hi he'.le) (show Repegs p' _ _ _ _ _ _ from by rw[hx]; exact hB.runs _ hi he') (fun _=> hq _) (fun U t=>hh t U) (δ:=fun _=>0) (s:=fun _=>0) (r:=fun _=>0) (fun _=>by simp) (fun _=>by simp) (fun j=>?_)
      refine ⟨∅,Set.finite_empty,?_⟩; rw[show profile _ _ =_ from (quietV : profile (R i).activities (g i)=0)]
      exact taped le_rfl le_rfl
end YM.Trace.Cask
