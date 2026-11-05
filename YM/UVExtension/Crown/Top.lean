import YM.UVExtension.Camp.Minuet
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
open Function Set Filter RG Lattice Wilson Precision
open Lamppost AnalyticBridge VerifiedReset Collection
open Oriel Oriel.Charted Push Push.AbsoluteSums Metric RG.Shoot Complex Finset
open scoped Topology ContDiff Matrix.Norms.Frobenius NNReal Classical
variable {G : Gauge} (h:G.Simple)(T:Levels G) (N:ℕ)(X:ℕ→Type)[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℂ (X i)]
namespace Cart
variable (V:Cart T N X)(r:ℕ)(hr:r ≤ N)
set_option quotPrecheck false
local notation "c'"=> tally T N X V
local notation "Λp"=> fun i=>pulse T i
noncomputable def pieces (m:ℕ)(z:PlotN N):ℂ:= ∑ i∈range m, if r≤ i then V.tally T N X z i else 0
noncomputable def locket (v:ℂ)(z:PlotN N): PlotN N := fun i=>if r≤ i.val then ((pulse T i.val:ℂ))⁻¹*((pulse T r:ℂ)*v-V.pieces T N X r i.val z) else 0
noncomputable def palms := ball (0:ℂ) (3*rad/4)
local notation "fl"=> (V.locket T N X r)
variable (hf:Fees T)(b:ℂ)(hb:b∈palms) {z u:PlotN N}(hv:z∈Harbor N)(hu:u∈Harbor N)
include h hf hv
lemma admits (m:ℕ)(hp:m ≤ N): ‖V.pieces T N X r m z‖ ≤ pulse T m*(soft/4):=by
    refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun i=> Camp.worth T (i+1)) (fun i hi=>?_)).trans (levy T h hf _))
    split; · exact V.rates T N X hv _ (lt_of_lt_of_le (mem_range.mp hi) hp)
    rw [norm_zero]; exact (worth_pos ..).le
include hb
lemma possibly : V.locket T N X r b z∈ Harbor N:=by
    apply mem_closedBall_zero_iff.mpr; refine (pi_norm_le_iff_of_nonneg (by norm_num [rad,rim])).2 fun i=>?_; unfold locket; split; swap; · norm_num [rad,rim]
    next ht =>
    rw [norm_mul,norm_inv,norm_real,Real.norm_of_nonneg (pulse_pos ..|>.le)]; apply (inv_mul_le_iff₀ (pulse_pos ..)).2; apply le_trans (norm_sub_le ..); rw [norm_mul,norm_real,Real.norm_of_nonneg (pulse_pos ..|>.le)]
    have hz: ‖b‖≤3*rad/4:= (mem_ball_zero_iff.mp hb).le; have he:=mul_le_mul (pulse_mono T h ht) hz (norm_nonneg _) (pulse_pos ..|>.le); have hk:=admits h T N X V r hf hv i.val (Nat.le_of_lt_succ i.2); unfold rad rim soft at *; linarith only [he,hk,pulse_pos T i.val]
omit hb
include hu
lemma drops : ‖fl b z-fl b u‖ ≤ soft*‖z-u‖:= by
    have hb₀ : 0 ≤ soft*‖z-u‖:=mul_nonneg (by norm_num [soft,rim]) (norm_nonneg _); refine pi_norm_le_iff_of_nonneg hb₀ |>.2 fun i=>?_ ; rw [Pi.sub_apply]; unfold locket; split_ifs; swap; · rwa [sub_zero,norm_zero]
    rw [←mul_sub,sub_sub_sub_cancel_left, norm_mul,norm_inv,norm_real,Real.norm_of_nonneg (pulse_pos ..|>.le), norm_sub_rev]; unfold pieces; rw [← Finset.sum_sub_distrib]; apply (inv_mul_le_iff₀ (pulse_pos ..)).2; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun i=> worth T (i+1)*‖z-u‖) (fun j hj=>?_)).trans ?_)
    · split_ifs; exact V.costs T N X hv hu _ (lt_of_lt_of_le (mem_range.mp hj) (Nat.le_of_lt_succ i.2)); rw [sub_zero,norm_zero]; exact mul_nonneg (worth_pos ..|>.le) (norm_nonneg _)
    rw [← sum_mul,← mul_assoc]; exact mul_le_mul_of_nonneg_right ((levy T h hf i.val).trans (mul_le_mul_of_nonneg_left (by norm_num [soft,rim]) (pulse_pos ..|>.le))) (norm_nonneg _)
omit h hf hv hu
lemma badge (s:Set ℂ)(hs:IsOpen s)(f:ℂ→PlotN N)(hM: MapsTo f s (Harbor N))(he:DifferentiableOn ℂ f s): DifferentiableOn ℂ (fun b=> V.locket T N X r b (f b)) s:=by
   intro z hz; apply differentiableWithinAt_pi.mpr; intro i; unfold locket; split; swap; · exact differentiableWithinAt_const _
   apply DifferentiableWithinAt.const_mul; apply (differentiableWithinAt_id.const_mul _).sub; refine DifferentiableWithinAt.fun_sum (fun j _=>?_); split; · exact V.bills T N X _ s f hs hM he z hz
   exact differentiableWithinAt_const _

private def liftV (b: ℂ) (hb:b∈palms) : Harbor N→ Harbor N:=fun z=> ⟨V.locket T N X r b z.val,V.possibly h T N X r hf b hb z.2⟩
local instance : Nonempty (↥(Harbor N)):= ⟨⟨0, harbor N⟩⟩
local instance : CompleteSpace (↥(Harbor N)):= isClosed_closedBall.completeSpace_coe
variable {b}
include h hf hb
private lemma liftVs: ContractingWith (1/2) (V.liftV h T N X r hf b hb):=by
   constructor; norm_num; refine LipschitzWith.of_dist_le_mul (fun z w=>?_)
   change dist (V.locket T N X r b z.val) (V.locket T N X r b w.val)≤ _*dist z.val w.val; simp only [dist_eq_norm]; exact (V.drops h T N X r hf b z.2 w.2).trans (mul_le_mul_of_nonneg_right (by norm_num [soft,rim]) (norm_nonneg _))

def chosenB : PlotN N := if g:b∈ palms then (ContractingWith.fixedPoint (V.liftV h T N X r hf b g) (liftVs h T N X V r hf g)).val else 0
-- arguments, includes hb? put separate
lemma zoned : let z:= V.chosenB h T N X r hf (b:=b); z∈Harbor N ∧ V.locket T N X r b z=z:= by
   unfold chosenB; rw [dif_pos hb]; intro z'; refine ⟨Subtype.coe_prop _,?_⟩; exact congr_arg Subtype.val ((liftVs h T N X V r hf hb).fixedPoint_isFixedPt)
lemma uniquely (he: V.locket T N X r b z=z)(hh: z∈ Harbor N): V.chosenB h T N X r hf (b:=b)=z:= by
   unfold chosenB; rw [dif_pos hb]; exact congr_arg Subtype.val ((liftVs h T N X V r hf hb).fixedPoint_unique (x:=⟨z,hh⟩) (Subtype.ext he)).symm
lemma wheels (k:ℕ): dist ((V.locket T N X r b)^[k] 0) (V.chosenB h T N X r hf (b:=b)) ≤ rad*(1/2)^k/(1-1/2):= by
    unfold chosenB; rw [dif_pos hb]; let f:= V.liftV h T N X r hf b hb; have hh:= V.liftVs h T N X r hf hb; let j: Harbor N:=⟨0,harbor N⟩
    have he := hh.apriori_dist_iterate_fixedPoint_le j k
    have hF (n:ℕ): (V.locket T N X r b)^[n] 0 = (f^[n] j).val:= by
      induction n with
      | zero=>rfl
      | succ n hn=> rw [iterate_succ_apply',iterate_succ_apply',hn]; rfl
    rw [hF]
    have hg: dist j (f j) ≤ rad:= by change dist (0:PlotN N) _ ≤ _; rw [dist_comm]; exact mem_closedBall.mp (f j).2
    exact he.trans (by push_cast; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hg (by positivity)) (by norm_num))
omit hb
lemma canyon : DifferentiableOn ℂ (fun b:ℂ=> V.chosenB h T N X r hf (b:=b)) (palms):=by
   let f i (b:ℂ):= (V.locket T N X r b)^[i] 0
   let s:=palms
   have hs(i): MapsTo (f i) s (Harbor N):=by intro b hb; induction i with | zero=> exact harbor N | succ i hi=> change _^[i+1] _∈_; rw [iterate_succ_apply']; exact V.possibly h T N X r hf b hb hi
   have ht(i):DifferentiableOn ℂ (f i) s:= by
      induction i with
      | zero=> exact differentiableOn_const _
      | succ i hi=> unfold f; simp_rw [iterate_succ_apply']; exact V.badge T N X r s isOpen_ball _ (hs i) hi
   have he: TendstoUniformlyOn f (fun b=> V.chosenB h T N X r hf (b:=b)) atTop s:=by
     refine Metric.tendstoUniformlyOn_iff.mpr (fun ε he=> ?_); have H:Tendsto (fun k:ℕ=>rad*(1/2)^k/(1-1/2)) atTop (𝓝 0):= by
       simpa only [mul_zero,zero_div] using (((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤ (1/2:ℝ)) (by norm_num)).const_mul rad).div_const ((1:ℝ)-1/2))
     filter_upwards [H.eventually (gt_mem_nhds he)] with i hi k hk; rw [dist_comm]; exact lt_of_le_of_lt (wheels h T N X V r hf hk i) hi
   exact he.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall ht) isOpen_ball

end Cart
end YM.UVExtension.Camp
