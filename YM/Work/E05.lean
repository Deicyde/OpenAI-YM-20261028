import YM.Bid.Energy
import YM.Slice.Strips
import YM.TimeKernel.Trace
import YM.Vac.Treasury


/-!
# Coarse row lower bounds in drows ( E)

Use the **ambient tubular chart**. Curvature in the row, converted back to matrix,
actually *is* the tangential projection of `U - 1`. So its squared-norm deficit
(chord versus curvature, same scale) prices only the squared *normal*
displacement. Need a real second-order bound on this displacement; take the
chart jet of `Gauge.focus`. Then apply in the clipped ranges after ℓ cancels. No
branch smoothness of the row assumed. Constants needed before L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.E05
open Filter Asymptotics Lattice RG Wilson Pressure
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators

section chart
attribute [local instance] Gauge.frobInner
variable (G : Gauge)

/-- The conversion in the defining representation, not assuming U near the identity. -/
theorem curvature_tangent (u : G.El) :
    G.lie.starProjection (G.mat u - 1) = G.colorMat (G.curvature u) := by
  let X := (1/2 : ℝ) • (G.mat u - G.mat u⁻¹)
  let H := G.mat u - 1 - X
  have hs : star H = H := by
    unfold H X
    simp only [star_sub, star_smul, star_trivial, star_one, G.mat_inv, star_star]
    module
  have hh : G.lie.starProjection H = 0 := by
    apply G.lie.starProjection_apply_eq_zero_iff.mpr
    intro w hw
    have h := real_inner_comm w H
    change (H * star w).trace.re = (w * star H).trace.re at h
    have hw' : star w = -w := G.generates_skew hw
    rw [hw', hs, mul_neg, Matrix.trace_neg, Complex.neg_re, Matrix.trace_mul_comm H w] at h
    change (w * star H).trace.re = 0
    rw [hs]; linarith
  change _ = G.colorMat (G.projectColor X)
  rw [G.colorMat_project, ← sub_eq_zero, ← map_sub]
  exact hh

private theorem norm_difference (u : G.El) : ‖G.mat u - 1‖ = G.colorScale * G.chord u := by
  simpa only [G.mat_one, inv_one, mul_one] using (chord_gap u (1:G.El)).symm

theorem sq_deficit (u : G.El) :
    G.colorScale^2 * (G.chord u ^ 2 - ‖G.curvature u‖^2) =
      ‖G.mat u - 1 - G.lie.starProjection (G.mat u - 1)‖^2 := by
  have h := G.lie.norm_sq_eq_add_norm_sq_starProjection (G.mat u - 1)
  rw [norm_difference, curvature_tangent, G.colorMat_norm,
      Submodule.starProjection_orthogonal_val] at h
  nlinarith only [h]

/-- Quadratic approximation, uniform for group elements in an ambient ball. -/
theorem normal_quadratic : ∃ (C r : ℝ), 0 < C ∧ 0 < r ∧ ∀ u : G.El,
    ‖G.mat u - 1‖ ≤ r →
      ‖G.mat u - 1 - G.lie.starProjection (G.mat u - 1)‖ ≤ C * ‖G.mat u - 1‖^2 := by
  have hn (u : G.El) : G.Nearest u (G.mat u) := fun v => by simp
  have he : G.mat (G.focus 1) = 1 := by
    rw [← (G.nearest_is_focus.self_of_nhds 1 (hn 1)), G.mat_one]
  obtain ⟨p,hp⟩ := G.focus_diff.analyticAt
  have h1 (x : G.Mat) : p 1 (fun _ => x) = G.lie.starProjection x :=
    DFunLike.congr_fun (hp.hasFDerivAt.unique G.focus_deriv.hasFDerivAt) x
  have h2 (x : G.Mat) : p.partialSum 2 x = 1 + G.lie.starProjection x := by
    rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_one,
      hp.coeff_zero, h1, he]
  obtain ⟨C, hC, hbig⟩ := (hp.isBigO_sub_partialSum_pow 2).exists_pos
  have ht : Tendsto (fun x : G.Mat => x - 1) (𝓝 1) (𝓝 0) := by
    simpa only [sub_self] using (show Continuous (fun x : G.Mat => x - 1) from by fun_prop).tendsto 1
  have hloc : ∀ᶠ x : G.Mat in 𝓝 1,
      ∀ u : G.El, x = G.mat u → ‖x - 1 - G.lie.starProjection (x - 1)‖ ≤ C * ‖x - 1‖^2 := by
    filter_upwards [ht.eventually hbig.bound, G.nearest_is_focus] with x hx hy u hu
    subst x
    change ‖G.mat (G.focus (1 + (G.mat u - 1))) - p.partialSum 2 (G.mat u - 1)‖ ≤
      C * ‖‖G.mat u - 1‖^2‖ at hx
    rw [add_sub_cancel, ← hy u (hn u), h2, Real.norm_of_nonneg (by positivity), sub_add_eq_sub_sub] at hx
    exact hx
  obtain ⟨r,hr,h⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hloc
  exact ⟨C,r,hC,hr,fun u hu => h (by rwa [Metric.mem_closedBall,dist_eq_norm]) u rfl⟩

/-- Lower bound in the *physical* normalization. Choose constants on G alone. -/
theorem curvature_lower : ∃ (K δ : ℝ), 0 < K ∧ 0 < δ ∧ ∀ u : G.El, G.chord u ≤ δ →
    G.chord u^2 - K * G.chord u^4 ≤ ‖G.curvature u‖^2 ∧
      3/4 * G.chord u^2 ≤ ‖G.curvature u‖^2 := by
  obtain ⟨C,r,hC,hr,hq⟩ := normal_quadratic G
  let D := G.colorScale
  let K := C^2 * D^2
  let b : ℝ := Real.sqrt (1 / (4*K))
  have hD : 0 < D := G.colorScale_pos
  have hK : 0 < K := by unfold K; positivity
  have hb : 0 < b := by unfold b; positivity
  refine ⟨K,min (r/D) b,hK,lt_min (by positivity) hb,?_⟩
  intro u hu
  have hg := G.chord_nonneg u
  obtain ⟨ha,hb'⟩ := le_min_iff.mp hu
  have ht := hq u (show ‖G.mat u - 1‖ ≤ r by
    rw [norm_difference, mul_comm]; exact (le_div_iff₀ hD).1 ha)
  have he := pow_le_pow_left₀ (norm_nonneg _) ht 2
  rw [← sq_deficit, norm_difference] at he
  have hm : G.chord u^2 - K * G.chord u^4 ≤ ‖G.curvature u‖^2 := by
    apply le_of_mul_le_mul_left (a:=D^2) ?_ (by positivity)
    unfold K D
    nlinarith only [he]
  refine ⟨hm, le_trans ?_ hm⟩
  have hδ : b^2 = 1 / (4*K) := Real.sq_sqrt (by positivity)
  have hu := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg hb' 2) hK.le
  rw [hδ, show K * (1 / (4*K)) = 1 / 4 by field_simp] at hu
  nlinarith only [mul_le_mul_of_nonneg_right hu (sq_nonneg (G.chord u))]
end chart

section clipping
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S)
  (R : ℕ) (V : Config G c) (s : ℝ) (i : Cell c)

open Pressure.Tube
open scoped Classical

/-- Coarse ℓ contributions cancel on both sides of kept, including cutoffs. -/
theorem workC_eq :
    let r := toll V i
    let a : ℝ := if r=0 then 1 else min 1 (s/r)
    T.workC R V s i = T.low.direct * (a - a^2/2) * ‖G.curvature (faceValue V i)‖^2 -
      PathData.clipped T.low s r := by
  intro r a
  let d := shoot T.low V i
  have hel : inner ℝ (T.vision R s V (i,true)) (T.Xn R V (i,true)) -
      ‖T.vision R s V (i,true)‖^2/2 = trunk T.down T.low R S.patch.L.val s V i := by
    by_cases h : PathData.kept T.low s i.1 V
    · simp [Tube.vision, Tube.Xn, thinned, plotted, trunk, h]
      ring
    · simp [Tube.vision, Tube.Xn, thinned, plotted, trunk, h]
  have hv : T.vision R s V (i,false) = a • d := by
    simp only [Tube.vision, thinned, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hx : T.Xn R V (i,false)=d := by simp [Tube.Xn, plotted, d]
  have hd : ‖d‖^2 = T.low.direct * ‖G.curvature (faceValue V i)‖^2 := by
    unfold d shoot
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt T.low.quadratic_pos.le]
  unfold Tube.workC crown
  rw [Fintype.sum_bool, hel, hv, hx, real_inner_smul_left,
    real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hd]
  dsimp only [r, toll]
  ring

lemma workC_small (h : toll V i ≤ s) (K : ℝ) (hK : 0 ≤ K)
    (hc : toll V i^2 - K * toll V i^4 ≤ ‖G.curvature (faceValue V i)‖^2) :
    -(T.low.direct*K/2*s^4) ≤ T.workC R V s i := by
  have hd := T.low.quadratic_pos
  have hr : 0 ≤ toll V i := G.chord_nonneg _
  have he : (if toll V i = 0 then 1 else min 1 (s/toll V i)) = 1 := by
    split
    · rfl
    next hn => rw [min_eq_left (by
      rw [le_div_iff₀ (lt_of_le_of_ne hr (Ne.symm hn)), one_mul]; exact h)]
  rw [workC_eq T, he, PathData.clipped, if_pos h]
  have hf := pow_le_pow_left₀ hr h 4
  nlinarith only [mul_le_mul_of_nonneg_left hc hd.le,
    mul_le_mul_of_nonneg_left hf (mul_nonneg hd.le hK)]

/-- In both next ranges the source of positive credit costs at least half a. -/
lemma workC_large (hs : 0 ≤ s) (hh : s < toll V i) :
    T.low.direct * (s / toll V i / 2) * ‖G.curvature (faceValue V i)‖^2 -
      T.low.linear*s*toll V i ≤ T.workC R V s i := by
  have hd := T.low.quadratic_pos
  have hr : 0 < toll V i := hs.trans_lt hh
  rw [workC_eq T, if_neg hr.ne', PathData.clipped, if_neg (not_le.2 hh)]
  have h : s / toll V i ≤ 1 := (div_le_one hr).mpr hh.le
  have hu : 0 ≤ s / toll V i := div_nonneg hs hr.le
  rw [min_eq_right h]
  apply sub_le_sub_right _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hd.le
  nlinarith only [mul_le_mul_of_nonneg_left h hu]

lemma workC_mid (hs : 0 ≤ s) (hh : s < toll V i)
    (hc : 3/4 * toll V i^2 ≤ ‖G.curvature (faceValue V i)‖^2) :
    T.low.direct/4*s*toll V i ≤ T.workC R V s i := by
  have hd := T.low.quadratic_pos
  have hr : 0 < toll V i := hs.trans_lt hh
  apply le_trans ?_ (workC_large T R V s i hs hh)
  have hb := mul_le_mul_of_nonneg_left hc (show 0 ≤ T.low.direct * (s / toll V i / 2) by positivity)
  have he : T.low.direct * (s / toll V i / 2) * (3/4 * toll V i^2) =
      3/8*T.low.direct*s*toll V i := by field_simp; ring
  have hi : T.low.linear*s*toll V i ≤ T.low.direct/8*s*toll V i := by
    apply mul_le_mul_of_nonneg_right _ hr.le
    apply mul_le_mul_of_nonneg_right _ hs
    linarith only [hd,T.low.kink]
  rw [he] at hb
  linarith only [hi,hb]
end clipping

open Pressure.Teller Pressure.Stores

lemma ultimately_cool (δ : ℝ) (h : 0 < δ) : ∀ᶠ x : ℝ in atTop, 0 ≤ temp x ∧ temp x ≤ δ := by
  filter_upwards [Vac.Numbers.uniform_loop, eventually_gt_atTop (1 / δ^3)] with x hx hy
  have hd : 0 < δ^3 := by positivity
  have ht : 0 < x := lt_trans (by positivity) hy
  refine ⟨by unfold temp; positivity,?_⟩
  have he : x*temp x^3 ≤ 1 := hx.2.1
  rw [div_lt_iff₀ hd] at hy
  by_contra! hh
  exact he.not_gt (hy.trans (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hh h.le (by norm_num)) ht))

theorem answer : YM.Bid.E05 := by
  intro G P
  obtain ⟨K,δ,hK,hδ,h⟩ := curvature_lower G
  have hp := P.below.clip.quadratic_pos
  refine ⟨δ,hδ,P.below.clip.direct*K/2,by positivity,fun L W => ⟨?_⟩⟩
  filter_upwards [ultimately_cool δ hδ] with x hx
  intro c f S _ _ T hT _ A U k V _ _
  refine ⟨fun i hs ht => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · exact workC_mid T _ V _ i hx.1 hs ((h _ ht).2)
  · rw [← hT.low]
    exact workC_small T _ V _ i hi K hK.le (h _ (hi.trans hx.2)).1
  · have he : temp x < toll V i := hx.2.trans_lt hi
    have ht : 0 < toll V i := hx.1.trans_lt he
    apply le_trans ?_ (workC_large T _ V _ i hx.1 he)
    have hd := T.low.quadratic_pos
    have hs := hx.1
    have hk : 0 ≤ T.low.direct * (temp x / toll V i / 2) * ‖G.curvature (faceValue V i)‖^2 := by positivity
    linarith only [hk]
end YM.Work.E05
