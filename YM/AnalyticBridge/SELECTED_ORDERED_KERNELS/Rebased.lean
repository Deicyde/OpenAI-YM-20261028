import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Lagrange
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Inverse
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Recenter
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Blocks
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.STATIONARY_UNIFORM.Calculus
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Motion



/-!
# Tools for chart budgets after a gauge-fixed extension in selected sectors

Do NOT express a finite perturbation by translating the ordinary additive
color chart at B. Compose with the gauge-only BCH-type germ and pay for its
jets as sup → sup maps (no volume costs). Use coarse and fine directions
rotated separately but by a shared gauge in applications. Pinned branch,
not differentiating this gauge choice! This doesn't obtain a *global* gauge
on the original V. The extension may be per-output slot.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Selected
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Next.SectorChange
  FreeResolvent Affine Push.Uniform
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k : ℕ}

attribute [local instance] Gauge.frobInner in
lemma project_star (x : G.Mat) : G.projectColor (star x) = - G.projectColor x := by
  apply eq_neg_of_add_eq_zero_left
  rw [← map_add]; apply G.colorMat_injective
  rw [map_zero,G.colorMat_project]
  apply G.lie.starProjection_apply_eq_zero_iff.mpr
  intro w hw
  let H := star x+x
  have hs : star H=H := by simp only [H,star_add,star_star,add_comm]
  have h := real_inner_comm w H
  change (H * star w).trace.re = (w * star H).trace.re at h
  rw [G.generates_skew hw, hs, mul_neg, Matrix.trace_neg, Complex.neg_re, Matrix.trace_mul_comm H w] at h
  change (w * star H).trace.re = 0
  rw [hs]; linarith

lemma curvature_project (g : G.El) : G.curvature g = G.projectColor (G.mat g) := by
  rw [Gauge.curvature, G.mat_inv,map_smul,map_sub,project_star]
  module

lemma paint_size (G : Gauge) (c : Side) : ‖(paint G c).toContinuousLinearMap‖ ≤ filePrice G := by
  apply ContinuousLinearMap.opNorm_le_bound _ ((file_pos G).trans' zero_le_one)
  intro z
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (zero_le_one.trans (file_pos G)) (norm_nonneg _))).mpr
  intro e
  exact (((file (G:=G) 1 (e.1,axisEquiv e.2)).le_opNorm z)).trans (mul_le_mul_of_nonneg_right (folder ..) (norm_nonneg _))

lemma back_size (G : Gauge) (c : Side) : ‖(paint G c).symm.toContinuousLinearMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun B => ?_
  rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i; exact (color_le (G:=G) ..).trans (norm_le_pi_norm B (edge i))
lemma tint_size (i : G.ColorIndex) : ‖PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b => (one_mul (‖b‖)).symm ▸ color_le b i
lemma adjoint_size (u : G.El) : ‖(G.adjoint u).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro b; change ‖G.adjoint u b‖ ≤ _; rw [G.norm_adjoint,one_mul]

private lemma fst_allows (G : Gauge) (c f : Side) (k : ℕ) : Allows k (Prod.fst : pair G c f → _) 0 1 := by
  let L := ContinuousLinearMap.fst ℝ (Vec G c 1) (Vec G f 1)
  apply allows_linear (L:=L) _ (by simp only [map_zero,norm_zero,zero_le_one])
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [one_mul]; exact norm_fst_le y
private lemma snd_allows (G : Gauge) (c f : Side) (k : ℕ) : Allows k (Prod.snd : pair G c f → _) 0 1 := by
  let L := ContinuousLinearMap.snd ℝ (Vec G c 1) (Vec G f 1)
  apply allows_linear (L:=L) _ (by simp only [map_zero,norm_zero,zero_le_one])
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [one_mul]; exact norm_snd_le y
lemma front_paint (G : Gauge) (c f : Side) (k : ℕ) : Allows k (fun z : pair G c f => paint G c z.1) 0 (filePrice G) := by
  have h := (fst_allows G c f k).linear (paint G c).toContinuousLinearMap (paint_size ..)
  rw [mul_one] at h; exact h
lemma rear_paint (G : Gauge) (c f : Side) (k : ℕ) : Allows k (fun z : pair G c f => paint G f z.2) 0 (filePrice G) := by
  have h := (snd_allows G c f k).linear (paint G f).toContinuousLinearMap (paint_size ..)
  rw [mul_one] at h; exact h

lemma swing_size (g : Site c → G.El) : ‖Motion.swing g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro b; rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    (fun e => (Motion.swing_size g b e).trans_le (norm_le_pi_norm b e))

abbrev insert (G : Gauge) (k : ℕ) := ContinuousLinearMap.single ℝ (fun _ : Fin (k+1) => G.Color) 0
lemma chain_insert (v : G.Color) : chain G (k+1) (insert G k v) = G.lieExp v := by
  change chain G k (Fin.tail (α:=fun _ => G.Color) (Pi.single (0:Fin (k+1)) v)) * _ = _
  rw [show (Fin.tail (α:=fun _ => G.Color) (Pi.single (0:Fin (k+1)) v): Panel G k)=0 from ?_,chain_zero]
  · simp [insert]
  funext i; change Pi.single 0 v i.succ=0; rw [Pi.single_eq_of_ne i.succ_ne_zero]
lemma insert_size (G : Gauge) (k : ℕ) : ‖insert G k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa [insert] using (Pi.norm_single (i:=(0:Fin (k+1))) (G:=fun _ => G.Color) x).le)

lemma allows_at {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] (i : ι) :
    ‖(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : ι => E) i)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [one_mul]; exact norm_le_pi_norm y i

variable (S) (k)
private def prep (B : Vec G c 1) (g : Site c → G.El) (i : Edge (Site c)) (z : pair G c f) :=
  (paint G c B i, insert G k (Motion.swing g (paint G c z.1) i))

def routing (B : Vec G c 1) (g : Site c → G.El) (z : pair G c f) : pair G c f :=
  ((paint G c).symm (fun i => moved G (k+1) (prep k B g i z)),
    (paint G f).symm (Motion.swing (constantGauge g S.ratio) (paint G f z.2)))

def freight (G : Gauge) := ∑ i ∈ Finset.range (k+1), charge G (k+1) i

def routeCost (G : Gauge) := max (composeCost k (freight k G) (max (radius G k) (filePrice G))) (filePrice G)

lemma route_nn (G : Gauge) : 0 ≤ routeCost k G := (zero_le_one.trans (file_pos G)).trans (le_max_right ..)

lemma prep_allows (g : Site c → G.El) {B : Vec G c 1} (i : Edge (Site c)) (h : ‖paint G c B i‖ < radius G k) :
    Allows k (prep k B g i (f:=f)) 0 (max (radius G k) (filePrice G)) := by
  apply (allows_const (n:=k) _ (h.le.trans (le_max_left ..))).pair
  have he := (((front_paint G c f k).linear _ (swing_size g)).linear _ (allows_at (E:=G.Color) i)).linear _ (insert_size G k)
  simp only [one_mul] at he
  exact he.mono (le_max_right ..)

@[simp] private lemma prep_zero (g : Site c → G.El) (B : Vec G c 1) (i : Edge (Site c)) : prep k B g i (0:pair G c f) = (paint G c B i,0) := by
  unfold prep; rw [Prod.fst_zero,map_zero,map_zero,Pi.zero_apply,map_zero]

variable {k} {B : Vec G c 1} (h : ∀ i, ‖paint G c B i‖ < radius G k) (g : Site c → G.El)
include h
@[simp] lemma routing_zero : routing S k B g 0 = (B,0) := by
  unfold routing; simp_rw [prep_zero, moved,displace,chain_zero,one_mul, fun i => ((frame_zone G k).choose_spec.2 _ (h i)).left]
  rw [ContinuousLinearEquiv.symm_apply_apply, Prod.snd_zero,map_zero,map_zero,map_zero]

lemma routing_allows : Allows k (routing S k B g) 0 (routeCost k G) := by
  have h' : 0 ≤ freight k G := Finset.sum_nonneg (fun i _ => charge_nn ..)
  have hc : 0 ≤ composeCost k (freight k G) (max (radius G k) (filePrice G)) := by
    have := radius_pos G k; unfold composeCost; positivity
  refine Allows.pair ?_ ?_
  · have hh i := (frame_zone G k).choose_spec.2 _ (h i)
    have ht := (allows_pi (f:=fun z : pair G c f => fun i => moved G (k+1) (prep k B g i z)) hc (fun i => (Allows.comp ?_ (prep_allows k g i (h i))))).linear _ (back_size G c)
    rotate_left
    · rw [prep_zero]
      exact ⟨(hh i).smooth _ le_rfl,fun j hj => ((hh i).norm _ _ le_rfl (Nat.le_succ_of_le hj)).trans (Finset.single_le_sum (fun i _ => charge_nn G (k+1) i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))⟩
    rw [one_mul] at ht; exact ht.mono (le_max_left ..)
  have hh := ((rear_paint G c f k).linear _ (swing_size (constantGauge g S.ratio))).linear _ (back_size G f)
  simp only [one_mul] at hh; exact hh.mono (le_max_right ..)

lemma routing_effect : ∀ᶠ z : pair G c f in 𝓝 0,
    (increment 1 (paint G c (routing S k B g z).1) = increment (increment 1 (paint G c B)) (Motion.swing g (paint G c z.1))) ∧
    paint G f (routing S k B g z).2 = Motion.swing (constantGauge g S.ratio) (paint G f z.2) := by
  have hr i := ((frame_zone G k).choose_spec.2 _ (h i)).right _ (le_refl (k+1))
  have ht i := ((prep_allows (f:=f) k g i (h i)).analytic.continuousAt.tendsto)
  simp_rw [prep_zero] at ht
  filter_upwards [eventually_all.mpr fun i => (ht i).eventually (hr i)] with z hz
  unfold routing; rw [ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]; constructor
  · funext i; simpa only [increment,Pi.one_apply,mul_one,displace,prep,chain_insert] using hz i
  rfl
end YM.SelectedOrderedKernels.Selected
