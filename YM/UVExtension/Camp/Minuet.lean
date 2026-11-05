import YM.UVExtension.Camp.Poise

/-! # Mesh- and period-uniform complex shooting. Unique trajectory in normalized
    ball (all meshes & arbitrary licensed data). Real slice property requires
    descent closures dealt with later on actual cost purchases. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
open Function Set Filter RG Lattice Wilson Precision
open Lamppost AnalyticBridge VerifiedReset Collection
open Oriel Oriel.Charted Push Push.AbsoluteSums Metric RG.Shoot Complex Finset
open scoped Topology ContDiff Matrix.Norms.Frobenius NNReal Classical
variable {G : Gauge} (h:G.Simple)(T:Levels G)
variable (N:ℕ)(X : ℕ→Type)[∀ i,NormedAddCommGroup (X i)] [∀ i,NormedSpace ℂ (X i)]

namespace Cart
variable (V:Cart T N X)(hf:Fees T) {b:ℂ}(hv:b∈Broad T) {z v:PlotN N}(hz:z∈Harbor N)(ht:v∈Harbor N)

private def harp (b: ℂ) (hv:b∈Broad T) : Harbor N→ Harbor N:=fun z=> ⟨V.veil T N X b z.val,V.access h T N X hf hv z.2⟩
lemma harbor (N:ℕ): 0∈ Harbor N:=mem_closedBall_self (by norm_num [rad,rim])
local instance : Nonempty (↥(Harbor N)):= ⟨⟨0, harbor N⟩⟩
local instance : CompleteSpace (↥(Harbor N)):= isClosed_closedBall.completeSpace_coe
include h hf hv
private lemma harps: ContractingWith (1/2) (V.harp h T N X hf b hv):=by
   constructor; norm_num; refine LipschitzWith.of_dist_le_mul (fun z w=>?_)
   change dist (V.veil T N X b z.val) (V.veil T N X b w.val)≤ _*dist z.val w.val; simp only [dist_eq_norm]; exact (V.dwindle h T N X hf z.2 w.2 b).trans (mul_le_mul_of_nonneg_right (by norm_num [soft,rim]) (norm_nonneg _))

def picked : PlotN N := if g:b∈ Broad T then (ContractingWith.fixedPoint (V.harp h T N X hf b g) (harps h T N X V hf g)).val else 0
-- arguments, includes hv? put separate
lemma laced : let z:= V.picked h T N X hf (b:=b); z∈Harbor N ∧ V.veil T N X b z=z:= by
   unfold picked; rw [dif_pos hv]; intro z'; refine ⟨Subtype.coe_prop _,?_⟩; exact congr_arg Subtype.val ((harps h T N X V hf hv).fixedPoint_isFixedPt)
lemma unique (he: V.veil T N X b z=z)(hh: z∈ Harbor N): V.picked h T N X hf (b:=b)=z:= by
   unfold picked; rw [dif_pos hv]; exact congr_arg Subtype.val ((harps h T N X V hf hv).fixedPoint_unique (x:=⟨z,hh⟩) (Subtype.ext he)).symm
lemma speed (k:ℕ): dist ((V.veil T N X b)^[k] 0) (V.picked h T N X hf (b:=b)) ≤ rad*(1/2)^k/(1-1/2):= by
    unfold picked; rw [dif_pos hv]; let f:= V.harp h T N X hf b hv; have hh:= V.harps h T N X hf hv; let j: Harbor N:=⟨0,harbor N⟩
    have he := hh.apriori_dist_iterate_fixedPoint_le j k
    have hF (n:ℕ): (V.veil T N X b)^[n] 0 = (f^[n] j).val:= by
      induction n with
      | zero=>rfl
      | succ n hn=> rw [iterate_succ_apply',iterate_succ_apply',hn]; rfl
    rw [hF]
    have hg: dist j (f j) ≤ rad:= by change dist (0:PlotN N) _ ≤ _; rw [dist_comm]; exact mem_closedBall.mp (f j).2
    exact he.trans (by push_cast; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hg (by positivity)) (by norm_num))
omit hv
lemma canon : DifferentiableOn ℂ (fun b:ℂ=> V.picked h T N X hf (b:=b)) (Broad T):=by
   let f i (b:ℂ):= (V.veil T N X b)^[i] 0
   let s:=Broad T
   have hs(i): MapsTo (f i) s (Harbor N):=by intro b hv; induction i with | zero=> exact harbor N | succ i hi=> change _^[i+1] _∈_; rw [iterate_succ_apply']; exact V.access h T N X hf hv hi
   have ht(i):DifferentiableOn ℂ (f i) s:= by
      induction i with
      | zero=> exact differentiableOn_const _
      | succ i hi=> unfold f; simp_rw [iterate_succ_apply']; exact V.warmth T N X s isOpen_ball _ (hs i) hi
   have he: TendstoUniformlyOn f (fun b=> V.picked h T N X hf (b:=b)) atTop s:=by
     refine Metric.tendstoUniformlyOn_iff.mpr (fun ε he=> ?_); have H:Tendsto (fun k:ℕ=>rad*(1/2)^k/(1-1/2)) atTop (𝓝 0):= by
       simpa only [mul_zero,zero_div] using (((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤ (1/2:ℝ)) (by norm_num)).const_mul rad).div_const ((1:ℝ)-1/2))
     filter_upwards [H.eventually (gt_mem_nhds he)] with i hi k hk; rw [dist_comm]; exact lt_of_le_of_lt (speed h T N X V hf hk i) hi
   exact he.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall ht) isOpen_ball
end Cart
end YM.UVExtension.Camp
namespace YM.UVExtension.Camp.Cart
open Function Set Filter RG Lattice Wilson Precision
open Lamppost AnalyticBridge VerifiedReset Collection
open Oriel Oriel.Charted Push Push.AbsoluteSums Metric RG.Shoot Complex Finset
open scoped Topology ContDiff Matrix.Norms.Frobenius NNReal Classical
variable {G : Gauge} (h:G.Simple)(T:Levels G)
variable (N:ℕ)(X : ℕ→Type)[∀ i,NormedAddCommGroup (X i)] [∀ i,NormedSpace ℂ (X i)]
variable (V:Cart T N X)(hf:Fees T) {b:ℂ}(hv:b∈Broad T) {z v:PlotN N}(hz:z∈Harbor N)(ht:v∈Harbor N)

def Light (w:PlotN N): Prop:=∀ i,(w i).im=0
include hv h
lemma gilded (he:b.im=0)(hy:∀ z:PlotN N,z∈Harbor N→ Light N z → ∀ i,(tally T N X V z i).im=0): Light N (V.picked h T N X hf (b:=b)):=by
   let f:=V.veil T N X b
   have hp (k:ℕ): f^[k] 0∈ Harbor N ∧ Light N (f^[k] 0):=by
      induction k with
      | zero=> exact ⟨harbor N,by simp [Light]⟩
      | succ k ih=>
        rw [iterate_succ_apply']; refine ⟨V.access h T N X hf hv ih.1,fun i=>?_⟩
        generalize hz:f^[k] 0=z at ih ⊢; unfold f veil; simp [← Complex.ofReal_inv, mul_im, he, show ∀ i,(tally T N X V z i).im=0 from hy _ ih.1 ih.2] -- f unfolded
   let g:= fun k:ℕ=> f^[k] 0
   have ht : Tendsto g atTop (𝓝 (V.picked h T N X hf (b:=b))):=by
      refine Metric.tendsto_nhds.mpr fun ε he=>?_; have hF:Tendsto (fun k:ℕ=>rad*(1/2)^k/(1-1/2)) atTop (𝓝 0):= by simpa only [mul_zero,zero_div] using (((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤ (1/2:ℝ)) (by norm_num)).const_mul rad).div_const ((1:ℝ)-1/2))
      filter_upwards [hF.eventually (gt_mem_nhds he)] with k hk; exact (speed h T N X V hf hv k).trans_lt hk
   have hX:= mem_iInter.mp (isClosed_iInter (f:=fun i:Fin (N+1)=> {z:PlotN N| (z i).im=0}) (fun i=> isClosed_eq (Complex.continuous_im.comp (continuous_apply i)) continuous_const) |>.mem_of_tendsto ht (Eventually.of_forall fun k=> by simp only [mem_iInter]; exact (hp k).2)) -- Light not def
   exact hX
end YM.UVExtension.Camp.Cart
