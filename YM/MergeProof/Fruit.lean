import YM.MergeProof.Heap
import YM.MergeProof.TeamKernel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Tonic
import YM.Planned.STATIONARY_JET_PORT.Tariff
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge   Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
variable [Fintype ι]
variable (q:ι→Hat B R) (v:V→ℝ)(k:Wing)
local notation "X"=> atKey q k
local notation "ι'"=> Mound q
set_option quotPrecheck false
local notation "W"=>fun i=> fare (q i) v
variable {e d:ℝ}(o:V→Site f)(b:ℕ)
structure Offer (o:V→Site f)(q:ι→Hat B R)(v:V→ℝ)(b:ℕ)(e d:ℝ):Prop where
    sites i:(q i).s.val.image o ⊆ (q i).M.crest
    budget : Ac.Hit (fun i=>(q i).M.crest) b (fun i=>fare (q i) v) e d
omit [Fintype ι] in
lemma Crew {p:Hat B R}(h:∀ i,0<v i): 0 ≤ fare p v:= mul_nonneg (timed p h) p.M.profit
variable (h:∀ i,0<v i)(hp:Offer o q v b e d)(hd:0≤e)
include h hp hd
lemma weight : ∑ i∈ X,W i ≤ d :=by
   have hx(i)(hi:i∈X): (q i).M.crest=k.support R:= by
      have hq: WKey (q i)=k:=(mem_filter.mp hi).2; exact congr_arg (fun i=> i.support R) hq
   by_cases he:(X).Nonempty; swap
   · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]; exact (tsum_nonneg (hp.budget 0).1).trans (hp.budget 0).2.2
   obtain ⟨i,hi⟩:=he; obtain ⟨j,hj⟩:= ((q i).shiny.image o).mono (hp.sites i); rw [hx i hi] at hj
   refine le_trans (Finset.sum_le_sum (s:=X) ?_) (Extra.Multi.Budget.cap (hp.budget j) _); intro i hi; dsimp only; rw [if_pos (show j∈ (q i).M.crest from (hx i hi).symm ▸ hj)]; exact le_mul_of_one_le_right (Crew v h) (Real.one_le_exp (mul_nonneg hd (by positivity)))

lemma scales : (∑ i:Rock q k, fare (rise q k i.val) v) ≤ Real.exp d* ∑ i∈X,W i:= by
   let w := W; let p:=∑ i∈X,w i
   have hq:p ≤ d:=weight q v k o b h hp hd
   have he(i):0≤w i:= Crew _ h
   have hu (i:Finset ι):0 ≤ ∏ j∈i,w j:= prod_nonneg fun j _=> he j
   have hv:0≤p:= sum_nonneg fun i _=> he i
   let name1(i:Rock q k):=i.val.val; let R:=(X).powerset.erase ∅
   simp_rw [tolls]; let Y(F:Finset ι):= ∏ j∈F,w j
   change ∑ i,Y (name1 i) ≤ _
   have hs:Injective name1:= Subtype.val_injective.comp Subtype.val_injective -- function syntax
   rw [← Finset.sum_image hs.injOn]
   calc
     _ ≤ ∑ i∈R,Y i := Finset.sum_le_sum_of_subset_of_nonneg (fun i hi=>by obtain ⟨j,hj,rfl⟩:= mem_image.mp hi; exact mem_erase.mpr ⟨j.1.property.1.ne_empty, mem_powerset.mpr j.val.property.2.1⟩) (fun i _ _ => hu i)
     _ ≤ Real.exp p-1 := by
          apply le_sub_iff_add_le.mpr; rw [show (1:ℝ)= Y ∅ from by simp [Y], show (∑ i∈R,Y i)+Y ∅= _ from Finset.sum_erase_add _ Y (empty_mem_powerset X)]
          unfold Y; rw [← Finset.prod_one_add, show p=∑ i∈X,w i from rfl, Real.exp_sum]; exact prod_le_prod (fun i _=> add_nonneg zero_le_one (he i)) (fun i _=> (add_comm ..).trans_le (Real.add_one_le_exp _))
     _ ≤ _ := by
          have hh:=Real.add_one_le_exp (-p); rw [Real.exp_neg] at hh; have hz:=Real.exp_pos p; rw [← one_div,le_div_iff₀ hz] at hh
          have hf:=Real.exp_monotone hq; change _ ≤ _ * p; nlinarith

lemma counts : Offer o (heap q) v b e (d+Real.exp d*d):=by
   refine ⟨fun i=> match i with | .inl i=> hp.sites i| .inr i=> fills q _ i.2.val o hp.sites,fun i=> ?_⟩
   let H:= heap q; let g z w:= if i∈z then w*Real.exp (e*coverNumber b z) else 0; let C j:= g ((q j).M.crest) (fare (q j) v); let c j:=g ((H j).M.crest) (fare (H j) v); have hm: SumBudget C d:=hp.budget i
   refine ⟨fun j=> ?_,Summable.of_finite,?_⟩
   · change 0≤ c j; unfold c g; split; exact mul_nonneg (Crew _ h) (Real.exp_pos _).le;rfl
   change (∑' j,c j)≤_; rw [tsum_fintype,Fintype.sum_sum_type]; apply add_le_add (Extra.Multi.Budget.cap hm univ)
   rw [Fintype.sum_sigma]
   let A:= fun i: ↥(logDeck q)=> Wing.logKey i.val; have he p: (∑ i: Rock q (A p), c (.inr ⟨p,i⟩)) ≤ Real.exp d * ∑ i∈ atKey q (A p),C i:=by
      let Y:= (A p).support R
      by_cases hz:i∈ Y
      · have hh(j) : c (.inr ⟨p,j⟩)=fare (rise q _ j.val) v*Real.exp (e*coverNumber b Y):= if_pos hz
        have hs(j)(hv:j∈ atKey q (A p)): C j=W j*Real.exp (e*coverNumber b Y):=by
           have hZ : (q j).M.crest= Y:= congr_arg (fun x:Wing=> x.support R) ((mem_filter.mp hv).2); unfold C g; rw [hZ,if_pos hz]
        rw [Finset.sum_congr rfl (fun i _=>hh i),Finset.sum_congr rfl hs, ← Finset.sum_mul,← Finset.sum_mul, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (scales q v _ o b h hp hd) (Real.exp_pos _).le
      rw [sum_eq_zero (fun j _=>by unfold c g; exact if_neg hz)]; exact mul_nonneg (Real.exp_pos _).le (sum_nonneg fun i _=> hm.1 i)
   apply le_trans (sum_le_sum (s:=Finset.univ) (fun j _=> he j)); rw [← mul_sum,← sum_biUnion]; exact mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap hm _) (Real.exp_pos _).le
   intro i hi j hj hn; refine Finset.disjoint_left.mpr fun x hx hj=> hn ?_; exact Subtype.ext (Wing.logKey.inj (((mem_filter.mp hx).2).symm.trans (mem_filter.mp hj).2)) -- parentheses
end YM.MergeProof.Menu
