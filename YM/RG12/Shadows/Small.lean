import YM.RG12.Shadows.Line
/-! Singular-route eligibility when χ overlaps. Taylor WITHOUT smooth
 hypothesis on actual Ingredient globally; restrict to the forced mouth.
 Don't extend Hard gates on any wrap or force contour. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open Metric Spins YM.AnalyticBridge.SectorAffine.Offset
open scoped ContDiff
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{f:E→F}
lemma parity_desk (y:E)(hy:‖y‖≤1)(A:ℝ)(h:∀ x,‖x‖≤1→Through 3 f x A)(hh:fderiv ℝ f 0=0):
    ‖f y - f (-y)‖ ≤ 2*A*‖y‖^3:=by
   have he{z:E}(hz:‖z‖≤‖y‖):‖fderiv ℝ f z+fderiv ℝ f (-z)‖ ≤ 2*A*‖y‖^2 := by
      have hk:= Spins.drift (j:=1) le_rfl h (hz.trans hy); simp only at hk -- let.intro
      -- iterated→CLM is iso
      let W:=(continuousMultilinearCurryFin1 ℝ E F)
      have hl(x) : iteratedFDeriv ℝ 1 f x=W.symm (fderiv ℝ f x):= by ext m; rw [iteratedFDeriv_one_apply]; rfl -- inspect
      simp only [hl,hh,map_zero,smul_zero,sub_zero,← W.symm.map_add, W.symm.norm_map] at hk
      exact hk.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) (by positivity [(h y hy).nonneg]))
   let g:E→E:=(- ·); let L:= -(ContinuousLinearMap.id ℝ E)
   have hv z (hz:‖z‖≤‖y‖) : HasFDerivAt (f-f∘g) (fderiv ℝ f z+fderiv ℝ f (-z)) z:=by
      have hd:= ((h z (hz.trans hy)).smooth.differentiableAt (by norm_num)).hasFDerivAt
      have hf := ((h (-z) (by rw [norm_neg]; exact hz.trans hy)).smooth.differentiableAt (by norm_num)).hasFDerivAt
      convert! hd.sub (hf.comp (f:=g) z (show HasFDerivAt g L z from L.hasFDerivAt)) using 1
      ext1 v; simp [L]
   have hl:= (convex_closedBall (0:E) ‖y‖).norm_image_sub_le_of_norm_fderiv_le (f:=(f-f∘g)) (fun _ hz=> (hv _ (mem_closedBall_zero_iff.mp hz)).differentiableAt) (fun _ hz=> by
       have hh:= mem_closedBall_zero_iff.mp hz; rw [(hv _ hh).fderiv]; exact he hh) (mem_closedBall_self (norm_nonneg y)) (mem_closedBall_zero_iff.mpr (le_refl ‖y‖))
   simpa only [Pi.sub_apply, Function.comp_apply,g,neg_zero,sub_self,sub_zero,pow_succ,mul_assoc] using! hl
end YM.RG12.Shadows
