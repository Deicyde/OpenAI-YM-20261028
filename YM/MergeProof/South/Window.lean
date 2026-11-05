import YM.MergeProof.South.Admit
import YM.MergeProof.South.Wakes
import YM.MergeProof.Wicket
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Clock

/-! purchase from finite intermediate assignment Y. weight d preserved in Wakes for yoga. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V : Type} [Fintype V][DecidableEq V]{B:Census V}{G:Gauge}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
section
variable (A:History G) (N p j:ℕ) {k:ℕ} {Z:Type*}[NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (I:Config G (A.S.side j p)→ Z)
local notation "S"=> A.S
set_option quotPrecheck false
local notation "P"=>A.levels.budget
local notation "R"=> A.rep N p
def gust (i)(hi:i ≤ j): Config G (A.S.side i p)→Z:=Nat.decreasingInduction (motive:=fun i _=> Config G (A.S.side i p)→Z) (fun m _ t=> (A.levels.clock.op m p).push (A.β N p (m+1)) t) I hi
lemma gust_base : gust A N p j I j le_rfl=I:=Nat.decreasingInduction_self ..
lemma gust_step (h:k<j) : gust A N p j I k h.le=(A.levels.clock.op k p).push (A.β N p (k+1)) (gust A N p j I (k+1) h):= Nat.decreasingInduction_succ_left ..
lemma gust_live (hI : Integrable I (prior G _))(hk:k ≤ j):Integrable (gust A N p j I k hk) (prior G _):=by
   induction hk using Nat.decreasingInduction with
   | self=> rw [gust_base]; exact hI
   | of_succ m hm IH=> rw [gust_step A N p j I hm]; exact StepData.push_integrable (A.levels.transition_mass ..) _ IH
variable [CompleteSpace Z]
lemma gust_sum (hI:Integrable I (prior G _))(hk:k ≤ j): (∫ U, gust A N p j I k hk U∂prior G _)=(∫ U, I U∂prior G _):=by
   induction hk using Nat.decreasingInduction with
   | self=>rw [gust_base]
   | of_succ m hm IH=>rw [gust_step A N p j I hm, StepData.push_integral (A.levels.transition_mass ..) _ (gust_live A N p j I hI hm),IH]
end
section
variable (A:History G) (r:ℕ→ℕ)(δ u:ℕ→ℝ)(D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m))
variable (N p:ℕ) {j k:ℕ} (e:j ≤ N) (o:∀ i:ℕ,V → Site (A.S.side i p))(w:ℕ →V→ℝ)
set_option quotPrecheck false
local notation "P"=>A.levels.budget
local notation "R"=> (A.rep N p)
variable (f:∀ m:ℕ,V  → Config G (A.S.side m p)→ℂ)(g:∀ m:ℕ,V→ℕ → Config G (A.S.side m p)→ℂ)
local notation "M"=> manifest A p N f g
local notation "T"=> tapes A p N g
variable {X:Config G (A.S.side j p)→Poly B}
    (h:A.Selected)(ht:Matchup A r δ p j k o w B) (hh:Moonlit A r δ u D)
    (hl:∀ i:V,Wakes A k j N p (fun m=>o m i) (fun m=>w m i) (fun m=>f m i) (fun m=>g m i) D e)
    (hQ:Served (A.rep N p j) (f j) (tapes A p N g j) X (o j) (w j) (A.levels.budget j).supportExponent 1) (he: Integrable X (prior G _))
local notation "C"=> gust A N p j X
include h ht hh hl hQ he
-- hQ usual purchase at retained exponent. can reduce by one or two at top intermediate if necessary.
set_option maxHeartbeats 800000 in
lemma window (m:ℕ)(hK:k ≤ m)(hm:m ≤ j): Served (R m) (f m) (T m) (C m hm) (o m) (w m) (A.levels.budget m).supportExponent 1:=by
   induction hm using Nat.decreasingInduction with
   | self =>rw [gust_base]; exact hQ
   | of_succ m hm IH=>
       have hm': k  ≤  m+1:= hK.trans m.le_succ
       let q:= gust A N p j X (m+1) hm; have hR : Integrable q (prior G _):= gust_live _ _ _ _ _ he hm
       have hc:=IH hm'; rw [gust_step A N p j X hm]; let P':=(A.levels.clock.op m p).push ((R (m+1)).beta) q
       have hN : m<N:=hm.trans_le e
       have hY(i):(fun U=> (q U).part (B.fire i))=M (m+1) i:=funext fun U=> hc.relay (fun i=> (hl i).stocked (m+1) hm' hm) ((h.represents _ _ _ hN).good.labels) U |>.1 i
       have hy(i):(fun U=>(P' U).part (B.fire i))= M m i:= (push_get (A.levels.transition_mass ..) hR _).trans (by rw [hY]; exact (hl i).feeds m hK hm|>.symm)
       choose ψ ν y x hf hs hX hD using fun i=> (hl i).sways m hK hm
       obtain ⟨v,g',hj,hb⟩:= hh.days N p m hN
       have hk:= ht.pins m hK hm
       let Z:= A.levels.clock.op m p; let x':=Z.ratio.parent ∘ o (m+1); have hP:x'=o m:=hk
       have hC:Occupancy x' (r m):=by rw [hP]; exact ht.occ _ hK hm.le
       have hA:Repegs x' (P m).B (fun i=>δ m*w (m+1) i) (w m) (1/2) 1 B:=by rw [hP]; exact ht.runs _ hK hm
       have hu(U i): (P' U).part (B.fire i)=coin (R m) (f m i) (g m i) U:= congr_fun (hy i) U
       have hΨ(i:V): ∃ Z': Set PhysicalNext.Repeat.Lotus.Wing, Z'.Finite∧Tale Z' (o (m+1) i) (x' i) 1 (f (m+1) i) (T (m+1) i) (T m i) (ν i) (y i) (x i) (D N p m hN):=by rw [hP]; exact ⟨ψ i,hf i,hD i⟩
       have hT := Duty.pre A N m p r h hN hb hj (ht.pos _ hm' hm) (ht.pos _ hK hm.le) (F':=f m) (δ:=ν) (s:=y) (r:=x) hc (by linarith only) (ht.next _ hK hm) hC hA (fun i=> (hl i).stocked _ hK hm.le) hu hs hX hΨ
       exact (congr_arg (fun (z: V → Site (A.S.side m p)) =>Served (R m) (f m) (T m) P' z (w m) (P m).supportExponent 1) hP).mp hT
end
end YM.MergeProof.Accent
