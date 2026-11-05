import YM.RG12.Spins.Effort
/-! Hessian-symmetry Taylor in *unscaled* deck. Prevents trading a scale for
 each pole derivative. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
noncomputable section
namespace YM.RG12.Spins
open Function Filter Metric Real YM.AnalyticBridge.SectorAffine.Offset
open scoped ContDiff
variable {E F K:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup K][NormedSpace ℝ K]
variable {C B R t r M:ℝ}
-- j+t symmetric.Now independent dimension
lemma drift {f:E→F}{n j:ℕ}(hj:j+2≤n)(h:∀ x,‖x‖≤R→Through n f x C){y:E}(hy:‖y‖≤R):
    let F:=iteratedFDeriv ℝ j f
    ‖F y + F (-y) - (2:ℝ) • F 0‖ ≤ 2*C*‖y‖^2 := by
   let g:=iteratedFDeriv ℝ j f; let G:=fderiv ℝ g
   intro Fg; change ‖g y+g (-y)-(2:ℝ) • g 0‖ ≤ _
   have h0 : 0≤R:= (norm_nonneg _).trans hy
   have hC:0 ≤ C:= (h y hy).nonneg
   have hk (x:E) (hx:‖x‖ ≤ R):ContDiffAt ℝ (2:ℕ∞ω) g x := (h x hx).smooth.iteratedFDeriv_right (by exact_mod_cast (show 2+j ≤ n by omega))
   let V:=iteratedFDeriv ℝ (j+1) f
   have he (x:E)(hx:‖x‖ ≤ R): DifferentiableAt ℝ V x := ((h x hx).smooth.iteratedFDeriv_right (m:=1) (by exact_mod_cast (show 1+(j+1)≤n by omega))).differentiableAt one_ne_zero
   have hp(x:E)(hx:‖x‖ ≤ R): ‖fderiv ℝ V x‖ ≤ C:=by unfold V; rw [norm_fderiv_iteratedFDeriv]; exact (h x hx).pay (j+2) hj
   have hV(x:E)(hx:‖x‖≤R):‖V x-V 0‖≤C*‖x‖:=by simpa only [sub_zero] using! (convex_closedBall (0:E) R).norm_image_sub_le_of_norm_fderiv_le (f:=V) (fun w hw=> he w (mem_closedBall_zero_iff.mp hw)) (fun w hw=>hp w (mem_closedBall_zero_iff.mp hw)) (mem_closedBall_self h0) (mem_closedBall_zero_iff.mpr hx)
   have hi(x:E)(hx:‖x‖≤R):‖G x-G 0‖≤C*‖x‖:=by
      have hjx (v): G v = (continuousMultilinearCurryLeftEquiv ℝ (fun _:Fin (j+1)=>E) F (V v)) := by
        unfold G g V; rw [iteratedFDeriv_succ_eq_comp_left]; simp
      let W:=continuousMultilinearCurryLeftEquiv ℝ (fun _:Fin (j+1)=>E) F; rw [hjx x,hjx 0];
      have ht:= W.isometry.dist_eq (V x) (V 0); simp_rw [dist_eq_norm] at ht; exact ht.trans_le (hV x hx)
   let Q x:=g x-G 0 x
   have ht (x:E)(hx:‖x‖≤R): ‖g x - g 0 - G 0 x‖ ≤ C*‖x‖^2:=by
     have hh(w)(hw : w ∈ closedBall (0:E) ‖x‖): HasFDerivAt Q (G w - G 0) w:= ((hk w ((mem_closedBall_zero_iff.mp hw).trans hx)).differentiableAt (by norm_num)).hasFDerivAt.sub (G 0).hasFDerivAt
     have H := (convex_closedBall (0:E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le (fun w hw=> (hh w hw).differentiableAt) (C:=C*‖x‖) (fun w hw=> by have he:= mem_closedBall_zero_iff.mp hw; rw [(hh w hw).fderiv]; exact (hi w (he.trans hx)).trans (mul_le_mul_of_nonneg_left he hC)) (mem_closedBall_self (norm_nonneg x)) (mem_closedBall_zero_iff.mpr (le_refl ‖x‖))
     dsimp only [Q] at H; rw [map_zero,sub_zero,sub_zero,mul_assoc,← sq] at H; rw [sub_right_comm]; exact H
   have hv:= ht y hy; have hx:= ht (-y) (norm_neg y ▸ hy)
   rw [show g y+g (-y)-(2:ℝ) • g 0 = (g y-g 0-G 0 y)+(g (-y)-g 0-G 0 (-y)) from by rw [map_neg,two_smul]; abel]
   apply (norm_add_le ..).trans; rw [norm_neg] at hx; linarith only [hv,hx]
end YM.RG12.Spins
