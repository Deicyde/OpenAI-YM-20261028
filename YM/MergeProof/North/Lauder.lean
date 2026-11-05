import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.MergeProof.Switch
import YM.Next.RANK.SealMix
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Reel
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Comparison
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge}(Q:Schedule)
-- control gap
lemma barbell (h : Q.Gentle) : Tendsto (fun i=> Q.scale (i+1)/Q.scale i) atTop (𝓝 1):=by
   have h' : (1:ℝ)= 1+0:= by norm_num
   refine ((tendsto_const_nhds (x:= (1:ℝ))).add h).congr' (?_) |> (h'.symm ▸ ·); filter_upwards [Q.divergent.eventually_gt_atTop 0] with i hi; rw [Q.scale_succ,add_div,div_self hi.ne']
lemma bob : StrictMono Q.scale:= by
   refine strictMono_nat_of_lt_succ fun i=> ?_; rw [Q.scale_succ]; exact lt_add_of_pos_right _ (Real.log_pos (by exact_mod_cast (show 1 < (Q.block i).val from lt_of_lt_of_le (by norm_num) (Q.block_large i))))
lemma trapeze (r:ℝ)(hr:1<r)(ht:Q.Gentle) : ∃ j:ℕ→ℕ,Tendsto j atTop atTop ∧ (∀ᶠ m in atTop,m+1< j m) ∧ Tendsto (fun i=>Q.scale (j i)/Q.scale i) atTop (𝓝 r):=by
   have he(i) : ∃ j:ℕ, r*Q.scale i≤ Q.scale j:= (Q.divergent.eventually_ge_atTop _).exists
   let j i:= Nat.find (he i); have hz(i): r*Q.scale i≤ Q.scale (j i):= Nat.find_spec (he i)
   have hv:∀ᶠ i in atTop,i+1<j i :=by
      filter_upwards [Q.divergent.eventually_gt_atTop 0,(barbell Q ht).eventually (gt_mem_nhds hr)] with i hi hi'; exact (bob Q).lt_iff_lt.mp (((div_lt_iff₀ hi).mp hi').trans_le (hz i))
   have hT:Tendsto j atTop atTop:= tendsto_atTop_mono' atTop (f₁:=fun i:ℕ=> i+1) (hv.mono fun i hi=> hi.le) (tendsto_add_atTop_nat 1) -- lemma edit
   refine ⟨j,hT,hv,?_⟩; let u i:= j i-1
   have hU : Tendsto u atTop atTop:= tendsto_atTop_mono' atTop (f₁:=id) (hv.mono fun i hi=> (show i ≤ u i by unfold u; omega)) tendsto_id
   have hy:= ((barbell Q ht).comp hU); refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (h:=fun i=> r*(Q.scale (u i+1)/Q.scale (u i))) tendsto_const_nhds (by simpa only [mul_one] using! hy.const_mul r) ?_ ?_
   · filter_upwards [Q.divergent.eventually_gt_atTop 0] with i hi; exact (le_div_iff₀ hi).mpr (hz i)
   · filter_upwards [Q.divergent.eventually_gt_atTop 0,(Q.divergent.comp hU).eventually_gt_atTop 0,hv] with i hi hK hv
     have hM:0<Q.scale (u i):=hK; have he':u i+1=j i:=by unfold u; omega
     have hP:Q.scale (u i)< r*Q.scale i:=lt_of_not_ge (Nat.find_min (he i) (show u i< j i by omega)); let v:=Q.scale (j i)/Q.scale (u i); have hp:v≥0:=div_nonneg ((hM.trans_le ((bob _).monotone (by omega))).le) hM.le
     rw [he',(div_le_iff₀ hi)]; exact le_trans (Eq.symm (show v*Q.scale (u i)= _ from div_mul_cancel₀ _ hM.ne')|>.le) ((mul_le_mul_of_nonneg_left hP.le hp).trans_eq (by change v*_ = r*v*_; ring))
end YM.MergeProof.Ribbons
