import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flux
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Point
import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Next.ROTATIONS.Journal
import YM.Planned.ATOM_REGULAR_ESTIMATE.CrossEffect
import YM.Push.PRICE_COMPILER.Post
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay
import YM.UVNext.PRICED_KERNELS.Echo

/-! Local `C^n` currencies at the stochastic E chart. Sup, not positional
ℓ². -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Metric Set AnalyticBridge.SectorAffine.Offset
open scoped Topology ContDiff BigOperators Classical
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {C D r t h : ℝ} {f g : E → F} {w : E → H} {x : E} {n : ℕ}

lemma sum_through (hf : Through n f x C) (hg : Through n g x D) : Through n (f+g) x (C+D) := by
  refine ⟨hf.smooth.add hg.smooth, fun j hj => ?_⟩
  rw [iteratedFDeriv_add_apply (hf.smooth.of_le (Nat.cast_le.mpr hj)) (hg.smooth.of_le (Nat.cast_le.mpr hj))]; exact (norm_add_le ..).trans (add_le_add (hf.pay j hj) (hg.pay j hj))
lemma pair_through (hf : Through n f x C) (hg : Through n w x C) : Through n (fun y => (f y,w y)) x C := by
  refine ⟨hf.smooth.prodMk hg.smooth,fun j hj => ?_⟩
  rw [iteratedFDeriv_prodMk hf.smooth hg.smooth (Nat.cast_le.mpr hj)]
  refine Planned.AtomRegular.op_le_of_unit hf.nonneg fun v hv => max_le ?_ ?_
  · simpa only [Finset.prod_const_one,mul_one] using! ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hf.pay _ hj) hv
  simpa only [Finset.prod_const_one,mul_one] using! ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hg.pay _ hj) hv
lemma pi_through {I : Type} [Fintype I] {f : E → I → F} (hC : 0 ≤ C) (h : ∀ i : I, Through n (fun y => f y i) x C) : Through n f x C := by
  have hg : ContDiffAt ℝ (n:ℕ∞ω) f x := contDiffAt_pi.mpr fun i => (h i).smooth
  refine ⟨hg,fun j hj => Planned.AtomRegular.op_le_of_unit hC fun v hv => (pi_norm_le_iff_of_nonneg hC).mpr fun i => ?_⟩
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : I => F) i
  rw [show iteratedFDeriv ℝ j f x v i= iteratedFDeriv ℝ j (L ∘ f) x v from congrArg (fun T : E [×j]→L[ℝ] F => T v) (L.iteratedFDeriv_comp_left hg (Nat.cast_le.mpr hj)).symm]
  simpa only [Finset.prod_const_one,mul_one] using! ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le ((h i).pay j hj) hv
lemma linear_through (L : F →L[ℝ] H) (hf : Through n f x C) (h : ‖L‖ ≤ D) : Through n (L ∘ f) x (D*C) := by
  refine ⟨L.contDiff.contDiffAt.comp _ hf.smooth,fun j hj => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left hf.smooth (Nat.cast_le.mpr hj)).trans (mul_le_mul h (hf.pay _ hj) (norm_nonneg _) ((norm_nonneg _).trans h))
lemma pre_through (L : H →L[ℝ] E) (h : ‖L‖ ≤ 1) (y : H) (hf : Through n f (L y) C) : Through n (f ∘ L) y C := by
  refine ⟨hf.smooth.comp _ L.contDiff.contDiffAt,fun j hj => ?_⟩
  rw [Push.Uniform.iter_lin_at (hf.smooth.of_le (Nat.cast_le.mpr hj))]; refine Planned.AtomRegular.op_le_of_unit hf.nonneg (fun v hv => ?_)
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]; simpa using! ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
    (hf.pay _ hj) (show ∀ i, ‖L (v i)‖ ≤ 1 from fun i => (L.le_opNorm _).trans (mul_le_one₀ h (norm_nonneg _) (hv i)))
lemma upright (L : E →L[ℝ] F) (n : ℕ) (h : ‖L‖ ≤ C) (hv : ‖x‖ ≤ 1) : Through n (fun x => L x) x C :=
  Through.control (Push.Uniform.allows_linear h ((L.le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg L) hv).trans h)))
lemma price_one (hf : Through n f x C) (hk : 1 ≤ n) : ‖fderiv ℝ f x‖ ≤ C := by rw [← norm_iteratedFDeriv_one]; exact hf.pay 1 hk
lemma price_two (hf : Through n f x C) (hk : 2 ≤ n) : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := by rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]; exact hf.pay 2 hk
lemma locate (hf : ∀ z : E, ‖z‖ ≤ t → Through n f z C) (h : 1 ≤ n) (h₀ : f 0=0) (hx : ‖x‖ ≤ t) : ‖f x‖ ≤ C*‖x‖ := by
  simpa only [h₀,sub_zero] using! (convex_closedBall (0:E) t).norm_image_sub_le_of_norm_fderiv_le (f:=f) (fun z hz => (hf z (mem_closedBall_zero_iff.mp hz)).smooth.differentiableAt (by exact_mod_cast (by omega : n≠0)))
    (fun z hz => price_one (hf _ (mem_closedBall_zero_iff.mp hz)) h) (mem_closedBall_self ((norm_nonneg x).trans hx)) (mem_closedBall_zero_iff.mpr hx)

structure Portrait (f : E → F) (L : E →L[ℝ] F) (n : ℕ) (h t C : ℝ) : Prop where
  uniform z : ‖z‖ ≤ t → Through n f z C
  home : f 0=0
  miss : ‖fderiv ℝ f 0-L‖ ≤ C*h

namespace Portrait
variable {L : E →L[ℝ] F}
lemma relax (hf : Portrait f L n h t C) (ht : r ≤ t) (hc : C ≤ D) (he : 0 ≤ h) : Portrait f L n h r D := ⟨(fun _ hy => (hf.uniform _ (hy.trans ht)).mono hc),hf.home,hf.miss.trans (mul_le_mul_of_nonneg_right hc he)⟩
lemma first_charge (hf : Portrait f L n h t C) (hk : 2 ≤ n) (hx : ‖x‖ ≤ t) : ‖fderiv ℝ f x-L‖ ≤ C*(h+‖x‖) := by
  have hF := (convex_closedBall (0:E) t).norm_image_sub_le_of_norm_fderiv_le (f:=fderiv ℝ f) (fun z hz => ((hf.uniform z (mem_closedBall_zero_iff.mp hz)).smooth.of_le
      (m:=2) (by exact_mod_cast hk)).fderiv_right (m:=1) (by norm_num) |>.differentiableAt (by norm_num))
    (fun z hz => price_two (hf.uniform _ (mem_closedBall_zero_iff.mp hz)) hk) (mem_closedBall_self ((norm_nonneg x).trans hx)) (mem_closedBall_zero_iff.mpr hx)
  apply (norm_sub_le_norm_sub_add_norm_sub _ (fderiv ℝ f 0) _).trans ((add_le_add hF hf.miss).trans_eq ?_)
  rw [sub_zero]; ring
lemma zeroth_charge (hf : Portrait f L n h t C) (hk : 2 ≤ n) (hx : ‖x‖ ≤ r) (ht : r ≤ t) : ‖f x-L x‖ ≤ C*(h+r)*r := by
  have hs y (hy : ‖y‖ ≤ r) := hf.uniform y (hy.trans ht)
  have h₀ : 0 ≤ r := (norm_nonneg x).trans hx
  have hd z (hz : z∈closedBall (0:E) r) := ((hs z (mem_closedBall_zero_iff.mp hz)).smooth.differentiableAt (by exact_mod_cast (by omega : n ≠ 0))).hasFDerivAt.sub L.hasFDerivAt
  have hC := (hs x hx).nonneg
  have hh := (convex_closedBall (0:E) r).norm_image_sub_le_of_norm_fderiv_le (f:=fun z => f z-L z) (fun z hz => (hd z hz).differentiableAt) (fun z hz => by
    have he := mem_closedBall_zero_iff.mp hz
    rw [show fderiv ℝ (fun z => f z-L z) z=fderiv ℝ f z-L from (hd _ hz).fderiv]; exact (hf.first_charge hk (he.trans ht)).trans (mul_le_mul_of_nonneg_left (add_le_add_right he _) hC)) (mem_closedBall_self h₀) (mem_closedBall_zero_iff.mpr hx)
  rw [hf.home,map_zero,sub_zero,sub_zero,sub_zero] at hh
  have he := (norm_nonneg _).trans hf.miss
  exact hh.trans (mul_le_mul_of_nonneg_left hx (by rw [mul_add]; exact add_nonneg he (mul_nonneg hC h₀)))
end Portrait
end YM.PhysicalNext.JointLoad.Heir
