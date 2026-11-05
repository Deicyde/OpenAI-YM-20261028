import YM.UVExtension.Camp.Lights
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
open Function Set Filter RG Lattice Wilson Precision
open Lamppost AnalyticBridge VerifiedReset Collection
open Oriel Oriel.Charted Push Push.AbsoluteSums Metric RG.Shoot Complex Finset
open scoped Topology ContDiff Matrix.Norms.Frobenius NNReal
variable {G : Gauge} (h:G.Simple)(T:Levels G)
variable (N:ℕ)(X : ℕ→Type)[∀ i,NormedAddCommGroup (X i)] [∀ i,NormedSpace ℂ (X i)]

-- closed ball, inner analytic reception. δ displacement (unscaled).
abbrev Broad := ball (0:ℂ) (flatTime T)
namespace Cart
variable (V:Cart T N X)

def veil (b:ℂ) (z:PlotN N): PlotN N:= fun i=> (pulse T i.val:ℂ)⁻¹*(b-∑ j∈ range i.val,V.tally T N X z j)
variable (hf:Fees T) {b:ℂ}(hv:b∈Broad T) {z v:PlotN N}(hz:z∈Harbor N)(ht:v∈Harbor N)
include h hf hz
lemma arrive (i:Fin (N+1)) : ‖∑ j∈range i.val,V.tally T N X z j‖ ≤ pulse T i.val*(soft/4):= (norm_sum_le ..).trans ((Finset.sum_le_sum (fun _ he=> V.rates T N X hz _ (lt_of_lt_of_le (Finset.mem_range.mp he) (Nat.le_of_lt_succ i.isLt)))).trans (levy T h hf _))
include hv in
lemma access : V.veil T N X b z∈Harbor N:= by
    apply mem_closedBall_zero_iff.mpr; refine pi_norm_le_iff_of_nonneg (by norm_num [rad,rim])|>.2 (fun i=> ?_)
    unfold veil; rw [norm_mul,norm_inv,norm_real, Real.norm_of_nonneg (pulse_pos ..|>.le)]
    apply (inv_mul_le_iff₀ (pulse_pos ..)).2; apply (norm_sub_le b _).trans
    have hp:‖b‖< flatTime T:= mem_ball_zero_iff.mp hv; unfold flatTime at hp; have ht:= arrive h T N X V hf hz i
    unfold rad soft rim at *; linarith only [ht,hp,pulse_mono T h (Nat.zero_le i.val),pulse_pos T i.val]
include ht in
lemma dwindle (b:ℂ): ‖V.veil T N X b z - V.veil T N X b v‖≤ soft*‖z-v‖:=by
    refine pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num [soft,rim]) (norm_nonneg (z-v)))|>.2 (fun i=>?_); simp only [Pi.sub_apply,veil,← mul_sub,sub_sub_sub_cancel_left];
    rw [norm_mul,norm_inv,norm_real,Real.norm_of_nonneg (pulse_pos ..|>.le),← sum_sub_distrib]
    apply (inv_mul_le_iff₀ (pulse_pos ..)).2; apply (norm_sum_le ..).trans
    refine le_trans (Finset.sum_le_sum (g:=fun j=> worth T (j+1)*‖z-v‖) (fun j he=>?_)) ?_
    · rw [norm_sub_rev]; exact V.costs T N X hz ht j (lt_of_lt_of_le (Finset.mem_range.mp he) (Nat.le_of_lt_succ i.isLt))
    rw [← sum_mul,← mul_assoc]; exact mul_le_mul_of_nonneg_right ((levy T h hf i.val).trans (mul_le_mul_of_nonneg_left (by norm_num [soft,rim]) (pulse_pos T _|>.le))) (norm_nonneg _)

omit h hf hz
lemma warmth (s:Set ℂ) (hs:IsOpen s) (f:ℂ→PlotN N)(hV: MapsTo f s (Harbor N))(he:DifferentiableOn ℂ f s): DifferentiableOn ℂ (fun b=> V.veil T N X b (f b)) s:=by
    intro z hz; apply differentiableWithinAt_pi.mpr; intro i; unfold veil; apply DifferentiableWithinAt.const_mul; exact differentiableWithinAt_id.sub (DifferentiableWithinAt.fun_sum (fun j _=> V.bills T N X j s f hs hV he z hz))
end Cart
end YM.UVExtension.Camp
