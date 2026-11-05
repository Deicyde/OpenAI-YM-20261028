import YM.FullVolume.Rank.Llama
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open MergeProof MergeProof.Matric ConnectedActivityE6 Lim Neptune
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{S:Desk G n}{A:Hol G}{P:BudgetPoint}{ι κ:Type}{E:Type}[NormedAddCommGroup E]
open FullVolume.Shadow
open Finset
variable [CompleteSpace E]
lemma fisher {f g:ℕ→ι→E}(hf:Sparse fun i j=> ‖f i j‖)(hg: Sparse fun i j=> ‖g i j‖)(he:∀ j, Tendsto (fun i=>f i j - g i j) atTop (𝓝 0)): Tendsto (fun i=> (∑' j,f i j)- ∑' j,g i j) atTop (𝓝 0):=by
    refine Metric.tendsto_nhds.mpr fun ε hε=>?_
    -- avoid paths. Sparse budget no weights
    let v i j:=f i j-g i j; have hv: Sparse (fun i j=> ‖v i j‖):=Sparse.smaller (hf.tug hg) (fun i j=> norm_nonneg _) (fun i j=> norm_sub_le ..)
    obtain ⟨C,hC⟩:= hv.bound; let t:= ε/4; have ht:0<t:=by unfold t; positivity
    obtain ⟨S,hS⟩:= hv.stalls t ht
    have hp : Tendsto (fun i=>∑ j∈S, ‖v i j‖) atTop (𝓝 0) := by simpa only [norm_zero,sum_const_zero] using tendsto_finsetSum S fun j _=> (he j).norm
    filter_upwards [hp.eventually (ge_mem_nhds ht)] with n hn
    rw [dist_zero_right,← Summable.tsum_sub ((hf.bound.choose_spec n).2.1.of_norm) ((hg.bound.choose_spec n).2.1.of_norm)]; change ‖∑' j,v n j‖< ε; refine ((norm_tsum_le_tsum_norm (hC n).2.1).trans (?_ : (∑' i,‖v n i‖) ≤ t+t)).trans_lt (by unfold t; linarith)
    refine (Push.AbsoluteSums.budget_of_sum (fun i=>norm_nonneg (v n i)) (fun T=>?_ )).2.2; rw [← sum_filter_add_sum_filter_not T (fun i=> i∈S)]; exact add_le_add ((sum_le_sum_of_subset_of_nonneg (fun i hi=> (mem_filter.mp hi).2) (fun i _ _ => norm_nonneg _)).trans (show ∑ i∈ S,‖v n i‖ ≤ t from hn)) (hS n _ (Finset.disjoint_left.mpr fun i hi hx=> (mem_filter.mp hx).2 hi))
variable {f g t s:ℕ→ι→ Config G n→ℂ} {X:ι→Support n} (h:Credit f g)
namespace Credit
include h in
lemma jerk (a:ι)(u:ℕ→ Config G n)(J:Ultrafilter ℕ)(he:(J:Filter ℕ) ≤ atTop) : Glints J (fun n=> f n a (u n)) (fun n=>g n a (u n)):= by
    obtain ⟨q,hq,hX⟩:=h.left.use; apply Glints.time _ ((h.polls a u).mono_left he); exact flowers (x:=0) (b:=hq.bound.choose) (Eventually.of_forall fun n=>by rw [dist_zero_right]; exact (hX n a _).trans (Push.AbsoluteSums.budget_single (hq.bound.choose_spec n) _))
lemma elementary (h:Credit f g)(V:ℕ→ Config G n): Tendsto (fun n=> (∑' i,f n i (V n))-∑' i,g n i (V n)) atTop (𝓝 0):=by
     obtain ⟨u,hu,U⟩:= h.left.use;obtain ⟨b,hb,B⟩:= h.right.use; exact fisher (hu.smaller (fun i j=> norm_nonneg _) (fun i j=> U ..)) (hb.smaller (fun i j=> norm_nonneg _) (fun i j=> B ..)) (fun i=> h.polls ..)
include h in
lemma pull (e:κ ↪ ι):Credit (fun i j=>f i (e j)) (fun i j=> g i (e j)):=by
     obtain ⟨u,hu,U⟩:= h.left.use; obtain ⟨b,hb,B⟩:= h.right.use; exact ⟨⟨_,hu.pull e,fun i j V=> U ..⟩,⟨_,hb.pull e,fun i j V=>B ..⟩,fun i=> h.polls _⟩
include h
lemma sumT (X:ι→κ) [Fintype κ]:Credit (fun n p V=> cram X (fun i=> f n i V) p) (fun n p V=>cram X (fun i=>g n i V) p):=by
     have hx {f:ℕ →ι→ Config G n →ℂ}(h:Bill f):Bill (fun n p V=> cram X (fun i=>f n i V) p):=by
         obtain ⟨u,hu,U⟩:= h.use; refine ⟨_,Sparse.constant Summable.of_finite (fun i:κ=> Push.AbsoluteSums.budget_nonneg (hu.bound.choose_spec 0)),fun i p V=>?_⟩
         exact (metric_cram X (hu.bound.choose_spec i).2.1 (fun i=> U ..) p).trans ((Local.sumBudget_subtype _ (hu.bound.choose_spec i)).2.2)
     exact ⟨hx h.left,hx h.right,fun i V=>(h.pull (Embedding.subtype (fun j=> X j=i))).elementary V⟩
lemma paired (hp:Credit t s): Credit (fun i j=> f i j*t i j) (fun i j=> g i j*s i j):=by
    have hv {f t:ℕ→ι→ Config G n→ℂ}(h:Bill f)(hp:Bill t):Bill (fun i j=> f i j*t i j):=by
       obtain ⟨v,hv,V⟩:= h.use; obtain ⟨w,hw,W⟩:= hp.use; obtain ⟨C,hC⟩:=hv.bound; refine ⟨_,hw.climb (Push.AbsoluteSums.budget_nonneg (hC 0)),fun i j u=>?_⟩; rw [Pi.mul_apply,norm_mul]; exact mul_le_mul ((V i j u).trans (Push.AbsoluteSums.budget_single (hC i) j)) (W i j u) (norm_nonneg _) (Push.AbsoluteSums.budget_nonneg (hC 0))
    refine ⟨hv h.left hp.left,hv h.right hp.right,fun i V=>?_⟩; exact (tendsto_iff_ultrafilter ..).mpr fun J hj=> ((h.jerk i V J hj).prods (hp.jerk i V J hj) continuous_mul).shrank
end Credit
namespace Base
variable {A B:ℕ→ Rep G n}{R: Desk G n}(hA:∀ n, Along R.orient (A n))(hB:∀ n, Along R.orient (B n))(hp:Angel (fun n=>(A n).activities.K) (fun n=> (B n).activities.K))

set_option quotPrecheck false
local notation "α"=> R.orient.p.threshold
local notation "s"=> Support n × Box n
include hA hp
variable (z:Support n)(j:Box n)
-- doesn't require nonnegative weights on K, only incl. tag.C.In!
lemma flagsK (hB:∀ n,Along R.orient (B n)) : Credit (fun n i=>grasp (A n).activities α z i j) (fun n i=>grasp (B n).activities α z i j):=by
    have h {A:ℕ→ Rep G n}(h:Vented (fun n=>(A n).activities.K)): Bill (fun n i=>grasp (A n).activities α z i j):=by
       obtain ⟨x,hx,V⟩:=h.sup;refine ⟨_,hx.arbitrary,fun n i Q=>?_⟩; unfold grasp; split
       · rw [norm_prod]; apply Finset.prod_le_prod (fun k _=>norm_nonneg _) (fun k _=>?_); rw [Complex.norm_real]; exact V ..
       rw [norm_zero]; exact hx.arbitrary.value ..
    refine ⟨h hp.a,h hp.b,fun i V=>?_⟩; let q(d:ℕ)(X:Rep G n)(U:Config G n):Prop:=Local.Packs X.activities z i ∧ fusionBox X.activities z i=j∧ j.1∩RG.flags α U=j.2 -- n issue
    refine (tendsto_iff_ultrafilter ..).mpr fun J hj=>?_ ; let Q n:= q n (A n) (V n)
    have hv : Glints J (fun n=> ∏ k∈i,(((A n).activities.K k (V n):ℝ):ℂ)) (fun n=> ∏ k∈i,(((B n).activities.K k (V n):ℝ):ℂ)) :=by simp_rw [← Complex.ofReal_prod]; exact (Frill.pears i (n:=0) (x:=(0:ℝ)) (fun k _=> Frill.bare (hp.glints hj k V))).crest.bin (fun _ _ => Complex.continuous_ofReal.continuousAt)
    apply ((Lim.switch hv ⟨0,tendsto_const_nhds,tendsto_const_nhds⟩ Q).shrank).congr'; filter_upwards with n
    have hg : (A n).activities.forced=(B n).activities.forced:= (hA n).force.symm.trans (hB n).force;have hy:Q n↔q n (B n) (V n):=by
      apply and_congr ?_ (by unfold fusionBox Push.Local.patch Push.Local.flagsFor; rw [hg]); constructor <;> rintro ⟨ha,hb,hc⟩ <;> (unfold Push.Local.Separate at *; simp only [Push.Local.patch] at hb hc; refine ⟨ha,?_,?_⟩)
      · unfold Push.Local.patch at hb; rw [hg] at hb; exact hb
      · rw [hg] at hc; exact hc
      · unfold Push.Local.patch at hb; rw [← hg] at hb; exact hb
      rw [←hg] at hc; exact hc
    unfold grasp; by_cases hk:Q n
    · rw [if_pos hk,if_pos hk]; congr! 1; all_goals first | rfl | rw [if_pos (hy.mp hk)]|rw [if_pos hk]
    · rw [if_neg hk,if_neg hk]; congr! 1; all_goals first|rfl|rw [if_neg (hy.not.mp hk)]|rw [if_neg hk]
end Base
end YM.FullVolume.Paint
