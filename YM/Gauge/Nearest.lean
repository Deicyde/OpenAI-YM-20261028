import YM.Gauge.Chart
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Nearest group point

We'll also use the normal equation to
fix the gauge in an alignment comparison. Statements work also for
subsingleton group and include every component (normal uses tangent,
optimization does not ignore disconnected components). Metric in results
is Frobenius. Avoid `dist` notation on group to keep matrix instance choices
clear. No selection regularity outside the small tube.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Gauge

open Function Filter Set NormedSpace Submodule
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff NNReal

attribute [local instance] frobInner
variable (G : Gauge)

def Nearest (u : G.El) (X : G.Mat) : Prop := ∀ v, ‖X-G.mat u‖ ≤ ‖X-G.mat v‖

theorem nearest_exists (X : G.Mat) : ∃ u, G.Nearest u X := by
  obtain ⟨u,-,hu⟩ := isCompact_univ.exists_isMinOn univ_nonempty (f := fun v : G.El => ‖X-G.mat v‖)
    (by apply Continuous.continuousOn; fun_prop)
  exact ⟨u, fun v => hu (mem_univ v)⟩

lemma nearest_left (v u : G.El) (X : G.Mat) : G.Nearest (v*u) (G.mat v * X) ↔ G.Nearest u X := by
  unfold Nearest
  rw [(Equiv.mulLeft v).surjective.forall]
  simp only [Equiv.coe_mulLeft, G.mat_mul, ← mul_sub, mul_frob_eq _ _ (G.mat_star_mul _)]

lemma nearest_right (v u : G.El) (X : G.Mat) : G.Nearest (u*v) (X * G.mat v) ↔ G.Nearest u X := by
  unfold Nearest
  rw [(Equiv.mulRight v).surjective.forall]
  simp only [Equiv.coe_mulRight, G.mat_mul, ← sub_mul, frob_mul_eq _ _ (G.mat_mul_star _)]

lemma nearest_normal_one {X : G.Mat} (h : G.Nearest 1 X) : X-1 ∈ G.lieᗮ := by
  intro Y hY
  have hf := G.colorMat_project_self hY
  let f (x : ℝ) := G.mat (G.lieExp (x • G.projectColor Y))
  have he : f 0 = 1 := by simp [f]
  have hd : HasDerivAt f Y 0 := by
    have H : HasDerivAt f (G.colorMat (G.projectColor Y)) 0 := by
      unfold f
      simp only [G.mat_lieExp,map_smul]
      simpa using! hasDerivAt_exp_smul_const (G.colorMat (G.projectColor Y)) (0 : ℝ)
    rwa [hf] at H
  have hg : IsLocalMin (fun x ↦ ‖f x-X‖^2) 0 := by
    refine Eventually.of_forall fun x => ?_
    dsimp only
    rw [he,norm_sub_rev,norm_sub_rev (f x)]
    apply (sq_le_sq₀ _ _).mpr
    · simpa only [G.mat_one] using h (G.lieExp (x • G.projectColor Y))
    all_goals positivity
  have hh := hg.hasDerivAt_eq_zero (hd.sub_const X).norm_sq
  have h0 : inner ℝ (1-X) Y = 0 := by simpa [he] using hh
  rwa [← neg_sub, inner_neg_right, real_inner_comm, neg_eq_zero]

lemma nearest_normal {u : G.El} {X : G.Mat} (h : G.Nearest u X) : star (G.mat u) * X - 1 ∈ G.lieᗮ := by
  have hd := (G.nearest_left u⁻¹ u X).mpr h
  rw [inv_mul_cancel, G.mat_inv] at hd
  exact G.nearest_normal_one hd

def tubular (x : G.Color × G.Normal) : G.Mat := G.mat (G.lieExp x.1) * (1 + (x.2 : G.Mat))

@[simp] theorem tubular_zero : G.tubular 0 = 1 := by simp [tubular]

theorem tubularDiff : ContDiffAt ℝ ω G.tubular 0 := by
  refine ContDiff.contDiffAt ?_; unfold tubular
  exact (G.exp_jet.comp contDiff_fst).mul (contDiff_const.add (G.lieᗮ.subtypeL.contDiff.comp contDiff_snd))

theorem tubularDeriv : HasFDerivAt G.tubular (G.addNormal : (G.Color × G.Normal) →L[ℝ] G.Mat) 0 := by
  let d := G.lieᗮ.subtypeL ∘L ContinuousLinearMap.snd ℝ G.Color G.Normal
  have he : HasFDerivAt (fun u : G.Color × G.Normal => (1 : G.Mat) + u.2.val) d 0 := d.hasFDerivAt.const_add _
  have hi : HasFDerivAt (fun a => G.mat (G.lieExp a)) G.colorMat.toContinuousLinearMap (0:G.Color × G.Normal).1 := G.expDiff_zero
  have hh := (hi.comp (0 : G.Color × G.Normal) hasFDerivAt_fst).mul' he
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro p; simp [d]
  exact add_comm (G.colorMat p.1) ↑p.2

private abbrev tube : OpenPartialHomeomorph (G.Color × G.Normal) G.Mat :=
    G.tubularDiff.toOpenPartialHomeomorph _ G.tubularDeriv (by simp)

def focus (X : G.Mat) : G.El := G.lieExp (G.tube.symm X).1

private lemma tube_in : (0 : G.Color × G.Normal) ∈ G.tube.source := ContDiffAt.mem_toOpenPartialHomeomorph_source ..

theorem focus_diff : ContDiffAt ℝ ω (fun x => G.mat (G.focus x)) 1 := by
  have h := G.tubularDiff.to_localInverse G.tubularDeriv (show ω ≠ (0 : WithTop ℕ∞) by simp)
  rw [G.tubular_zero] at h
  exact G.exp_jet.contDiffAt.comp _ (contDiffAt_fst.comp (1 : G.Mat) h)

private lemma focuses (b : G.Mat → G.El) (h : ∀ X, G.Nearest (b X) X) : b =ᶠ[𝓝 1] G.focus := by
  let m (x) := G.mat (b x)
  have hj : Tendsto m (𝓝 (1:G.Mat)) (𝓝 1) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    apply squeeze_zero (fun x => norm_nonneg _) (g := fun x => 2*‖x-1‖)
    · intro x
      have he : ‖m x-x‖ ≤ ‖x-1‖ := by rw [norm_sub_rev]; exact h x 1
      exact (norm_sub_le_norm_sub_add_norm_sub _ x _).trans (by linarith)
    simpa using! (show Continuous fun x : G.Mat => 2*‖x-1‖ from by fun_prop).tendsto (1:G.Mat)
  have hn : Tendsto b (𝓝 1) (𝓝 1) := (G.continuous_mat.isClosedEmbedding G.mat_injective).tendsto_nhds_iff.mpr hj
  have hg : Tendsto G.plog (𝓝 1) (𝓝 0) := by simpa only [plog_one] using! G.plog_diff.continuousAt.tendsto
  let u (x : G.Mat) : G.Normal := ⟨_, G.nearest_normal (h x)⟩
  have hu : Tendsto u (𝓝 1) (𝓝 0) := by
    apply (show Topology.IsEmbedding (Subtype.val : G.Normal → G.Mat) from Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr
    simpa only [star_one, one_mul, sub_self, coe_zero] using!
      (hj.star.mul (tendsto_id (x := 𝓝 (1:G.Mat)))).sub (tendsto_const_nhds (x := (1:G.Mat)))
  let q (x) := (G.plog (m x),u x)
  have hq : Tendsto q (𝓝 1) (𝓝 (0:G.Color × G.Normal)) := (hg.comp hj).prodMk_nhds hu
  filter_upwards [hq.eventually (G.tube.open_source.mem_nhds G.tube_in), hn.eventually G.plog_right] with x hx hz
  have ht : G.tubular (q x)=x := by
    change G.mat (G.lieExp (G.plog (G.mat (b x)))) * (1+(star (G.mat (b x))*x-1))=x
    rw [hz, add_sub_cancel, ← mul_assoc,G.mat_mul_star,one_mul]
  unfold focus; rw [show G.tube.symm x = q x from by
    calc
      _ = G.tube.symm (G.tubular (q x)) := by rw [ht]
      _ = q x := G.tube.left_inv hx]
  exact hz.symm

theorem nearest_is_focus : ∀ᶠ x : G.Mat in 𝓝 1, ∀ u, G.Nearest u x → u = G.focus x := by
  classical
  let H (x : G.Mat) : Prop := ∃ u, G.Nearest u x ∧ u ≠ G.focus x
  let b (x : G.Mat) := if h : H x then h.choose else (G.nearest_exists x).choose
  have he (x : G.Mat) : G.Nearest (b x) x := by
    unfold b; split
    next h => exact (Exists.choose_spec h).1
    exact (G.nearest_exists _).choose_spec
  filter_upwards [G.focuses b he] with x hx u h
  by_contra! hu
  have hd : H x := ⟨u,h,hu⟩
  exact (Exists.choose_spec hd).2 (by simpa only [b, dif_pos hd] using hx)

theorem nearest_tube : ∃ δ : ℝ, 0 < δ ∧ ∀ X : G.Mat, ∀ v, ‖X-G.mat v‖ < δ → ∃! u, G.Nearest u X := by
  obtain ⟨δ,h,hδ⟩ := Metric.mem_nhds_iff.mp G.nearest_is_focus
  refine ⟨δ,h,fun X v hx => ?_⟩
  let U := G.mat v⁻¹ * X
  have he : U ∈ Metric.ball 1 δ := by
    rw [Metric.mem_ball,dist_eq_norm, ← G.mat_one, ← inv_mul_cancel v, G.mat_mul]
    change ‖G.mat v⁻¹ * X-G.mat v⁻¹ * G.mat v‖<δ
    rw [← mul_sub, mul_frob_eq _ _ (G.mat_star_mul _)]
    exact hx
  obtain ⟨u,hu⟩ := G.nearest_exists X
  refine ⟨u,hu,fun z hz => ?_⟩
  exact mul_left_cancel ((hδ he _ ((G.nearest_left v⁻¹ _ _).mpr hz)).trans
    (hδ he _ ((G.nearest_left v⁻¹ _ _).mpr hu)).symm)

theorem focus_deriv : HasStrictFDerivAt (fun x => G.mat (G.focus x)) G.lie.starProjection 1 := by
  apply G.focus_diff.hasStrictFDerivAt' _ (by simp)
  have h : HasFDerivAt G.tube.symm (G.addNormal.symm : G.Mat →L[ℝ] (G.Color × G.Normal)) (1:G.Mat) := by
    rw [← G.tubular_zero]
    exact (G.tubularDiff.hasStrictFDerivAt' G.tubularDeriv (by simp)).to_localInverse.hasFDerivAt
  have hz : G.tube.symm 1 = 0 := by rw [← G.tubular_zero]; exact G.tube.left_inv G.tube_in
  have he : HasFDerivAt (fun c => G.mat (G.lieExp c)) G.colorMat.toContinuousLinearMap
      ((Prod.fst ∘ G.tube.symm) 1) := by rw [Function.comp_apply,hz]; exact G.expDiff_zero
  have hu := he.comp 1 (hasFDerivAt_fst.comp 1 h)
  convert! hu using 1
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨⟨a,b⟩,rfl⟩ := G.addNormal.surjective x
  change G.lie.starProjection _ = G.colorMat (G.addNormal.symm _).1
  rw [G.addNormal.symm_apply_apply,G.addNormal_apply, map_add,
    starProjection_eq_self_iff.mpr (G.colorMat_mem _), (G.lie.starProjection_apply_eq_zero_iff).mpr b.property, add_zero]

theorem nearest_approximate (ε : ℝ≥0) (h : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧
    ∀ X Y, ‖X-1‖ < δ → ‖Y-1‖ < δ → ∀ u v, G.Nearest u X → G.Nearest v Y →
      ‖G.mat u - G.mat v - G.lie.starProjection (X-Y)‖ ≤ ε * ‖X-Y‖ := by
  obtain ⟨s,hS,H⟩ := G.focus_deriv.approximates_deriv_on_nhds (Or.inr h)
  obtain ⟨δ,hp,hδ⟩ := Metric.mem_nhds_iff.mp (inter_mem hS G.nearest_is_focus)
  refine ⟨δ,hp,fun X Y hx hy u v hu hv => ?_⟩
  have ei := hδ (show X ∈ Metric.ball (1:G.Mat) δ from by rwa [Metric.mem_ball,dist_eq_norm])
  have ej := hδ (show Y ∈ Metric.ball (1:G.Mat) δ from by rwa [Metric.mem_ball,dist_eq_norm])
  rw [ei.2 u hu, ej.2 v hv]
  exact H X ei.1 Y ej.1
end YM.Gauge
