import YM.Gauge.Colors
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Exponential patches for the closed representation image

No connectedness assumption. Use the real matrix Lie algebra *derived* from
one-parameter subgroups. Orthogonal slice proof: consider exp C times exp N
where N is Frobenius orthogonal. Inverse function near (0,0), and if those
images are group elements then necessarily N is zero -- a sequence of bad
points would give, using powers near 0, a new Lie alg direction off the slice.
A fixed ambient analytic inverse provides a left inverse local for increments
and right inverse to group elements near identity. No global log claims!
-/

set_option autoImplicit false
noncomputable section
namespace YM.Gauge

open Function Filter Set NormedSpace Submodule
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators

attribute [local instance] frobInner
variable (G : Gauge)

abbrev Normal := ↥G.lieᗮ

lemma exp_inv_range {X : G.Mat} (h : exp X ∈ range G.mat) : exp (-X) ∈ range G.mat := by
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  obtain ⟨u,hu⟩ := h
  refine ⟨u⁻¹, ?_⟩
  have he : exp X * exp (-X) = 1 := by
    have H : exp (X + -X) = exp X * exp (-X) := exp_add_of_commute ((Commute.refl X).neg_right)
    rw [← H]; simp
  calc
    _ = G.mat u⁻¹ * 1 := by rw [mul_one]
    _ = G.mat u⁻¹ * (exp X * exp (-X)) := by rw [he]
    _ = exp (-X) := by rw [← hu, ← mul_assoc, ← G.mat_mul, inv_mul_cancel, G.mat_one, one_mul]

lemma direction_in_lie (X : ℕ → G.Mat) (u : G.Mat)
    (he : ∀ n, exp (X n) ∈ range G.mat) (hn : Tendsto X atTop (𝓝 0))
    (hp : ∀ n, X n ≠ 0) (hu : Tendsto (fun n => ‖X n‖⁻¹ • X n) atTop (𝓝 u)) : u ∈ G.lie := by
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  have hs (t : ℝ) (ht : 0 ≤ t) : exp (t • u) ∈ range G.mat := by
    let k n := Nat.floor (t/‖X n‖)
    let s (n : ℕ) : ℝ := (k n : ℝ) * ‖X n‖
    have hb : Tendsto s atTop (𝓝 t) := by
      have hk : Tendsto (fun n => t - ‖X n‖) atTop (𝓝 t) := by simpa using! (tendsto_const_nhds (x := t)).sub hn.norm
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le hk tendsto_const_nhds
      · intro n
        have h := (div_lt_iff₀ (norm_pos_iff.mpr (hp n))).mp (Nat.lt_floor_add_one (t/‖X n‖))
        change t-‖X n‖ ≤ (Nat.floor (t/‖X n‖) : ℝ) * ‖X n‖
        linarith
      · intro n
        exact (le_div_iff₀ (norm_pos_iff.mpr (hp n))).mp (Nat.floor_le (div_nonneg ht (norm_nonneg _)))
    have h : Tendsto (fun n => exp (s n • (‖X n‖⁻¹ • X n))) atTop (𝓝 (exp (t • u))) := exp_continuous.continuousAt.tendsto.comp (hb.smul hu)
    apply G.closed_matrices.mem_of_tendsto h
    refine Eventually.of_forall fun n ↦ ?_
    rw [smul_smul, show s n * ‖X n‖⁻¹ = k n by unfold s; rw [mul_assoc,mul_inv_cancel₀ (norm_pos_iff.mpr (hp n)).ne',mul_one], Nat.cast_smul_eq_nsmul, show exp (k n • X n) = exp (X n) ^ k n from exp_nsmul (k n) (X n)]
    obtain ⟨v,hv⟩ := he n
    refine ⟨v^(k n),?_⟩
    let b : G.El →* G.Mat := { toFun := G.mat, map_one' := rfl, map_mul' := G.mat_mul }
    change b (v^k n) = _
    rw [map_pow]; change G.mat v ^ _ = _; rw [hv]
  rw [mem_lie]
  intro t
  rcases le_total 0 t with h | h
  · exact hs t h
  simpa using G.exp_inv_range (hs (-t) (by linarith))

lemma isolates : ∀ᶠ x : G.Normal in 𝓝 0, exp (x : G.Mat) ∈ range G.mat → x = 0 := by
  by_contra hh
  simp only [not_eventually, Classical.not_imp] at hh
  let S := {x : G.Normal | exp (x : G.Mat) ∈ range G.mat ∧ x ≠ 0}
  have he : (0 : G.Normal) ∈ closure S := mem_closure_iff_frequently.mpr hh
  haveI hsec : FirstCountableTopology G.Normal := by
    haveI : FirstCountableTopology G.Mat := inferInstanceAs (FirstCountableTopology (Fin _ → Fin _ → ℂ))
    exact (show Topology.IsEmbedding (Subtype.val : G.Normal → G.Mat) from Topology.IsEmbedding.subtypeVal).firstCountableTopology
  obtain ⟨X,hX,h⟩ := mem_closure_iff_seq_limit.mp he
  let Z (n : ℕ) : G.Normal := ‖X n‖⁻¹ • X n
  have hu (n) : Z n ∈ Metric.sphere (0 : G.Normal) 1 := by
    dsimp only [Z]
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_pos_iff.mpr (show X n ≠ 0 from (hX n).2)).ne']
  haveI : ProperSpace G.Normal := FiniteDimensional.proper ℝ _
  obtain ⟨Y,hY,b,hb,he⟩ := (isCompact_sphere (0 : G.Normal) 1).isSeqCompact hu
  have hl : (Y : G.Mat) ∈ G.lie := G.direction_in_lie (fun n => ((X (b n)):G.Mat)) Y
    (fun n => (hX _).1) ((continuous_subtype_val.tendsto _).comp (h.comp hb.tendsto_atTop))
    (fun n hu => (hX _).2 (Subtype.ext hu)) ((continuous_subtype_val.tendsto _).comp he)
  have hy : Y = 0 := Subtype.ext (show _ = 0 from (Eq.le (disjoint_iff.mp G.lie.isCompl_orthogonal.disjoint)) ⟨hl,Y.property⟩)
  simp [hy] at hY

def addNormal : (G.Color × G.Normal) ≃L[ℝ] G.Mat := LinearEquiv.toContinuousLinearEquiv
    ((G.colorIso.prodCongr (LinearEquiv.refl ℝ G.Normal)).trans (G.lie.prodEquivOfIsCompl G.lieᗮ G.lie.isCompl_orthogonal))

@[simp] theorem addNormal_apply (x : G.Color × G.Normal) : G.addNormal x = G.colorMat x.1 + x.2 := rfl

@[fun_prop] theorem contDiff_exp : ContDiff ℝ ω (NormedSpace.exp : G.Mat → G.Mat) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x; exact (exp_analytic x).contDiffAt

@[fun_prop] theorem exp_jet : ContDiff ℝ ω (fun a : G.Color => G.mat (G.lieExp a)) := by
  simp only [G.mat_lieExp]
  exact G.contDiff_exp.comp G.colorMat.toContinuousLinearMap.contDiff

def splitNormal (x : G.Color × G.Normal) : G.Mat := G.mat (G.lieExp x.1) * exp (x.2 : G.Mat)

@[simp] theorem mat_lieExp_zero : G.lieExp 0 = 1 := by apply G.mat_injective; simp

@[simp] theorem splitNormal_zero : G.splitNormal 0 = 1 := by simp [splitNormal]

theorem splitDiff : ContDiffAt ℝ ω G.splitNormal 0 := by
  refine ContDiff.contDiffAt ?_
  unfold splitNormal; apply ContDiff.mul
  · exact G.exp_jet.comp contDiff_fst
  exact G.contDiff_exp.comp (G.lieᗮ.subtypeL.contDiff.comp contDiff_snd)

theorem expDiff_zero : HasFDerivAt (fun a => G.mat (G.lieExp a)) G.colorMat.toContinuousLinearMap 0 := by
  have h := (show HasFDerivAt NormedSpace.exp (1 : G.Mat →L[ℝ] G.Mat) 0 from hasFDerivAt_exp_zero)
  simp only [G.mat_lieExp]
  have he : HasFDerivAt NormedSpace.exp (1 : G.Mat →L[ℝ] G.Mat) (G.colorMat.toContinuousLinearMap (0:G.Color)) := by simpa using h
  convert! he.comp (0 : G.Color) G.colorMat.toContinuousLinearMap.hasFDerivAt using 1

theorem splitDeriv : HasFDerivAt G.splitNormal (G.addNormal : (G.Color × G.Normal) →L[ℝ] G.Mat) 0 := by
  let d := G.lieᗮ.subtypeL ∘L ContinuousLinearMap.snd ℝ G.Color G.Normal
  have he : HasFDerivAt NormedSpace.exp (1 : G.Mat →L[ℝ] G.Mat) (d 0) := by rw [map_zero]; exact hasFDerivAt_exp_zero
  have h := he.comp (0:G.Color × G.Normal) d.hasFDerivAt
  have hi : HasFDerivAt (fun a => G.mat (G.lieExp a)) G.colorMat.toContinuousLinearMap (0:G.Color × G.Normal).1 := G.expDiff_zero
  have hh := (hi.comp (0 : G.Color × G.Normal) hasFDerivAt_fst).mul' h
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro p; simp [d]
  exact add_comm (G.colorMat p.1) ↑p.2

private abbrev coord : OpenPartialHomeomorph (G.Color × G.Normal) G.Mat :=
    G.splitDiff.toOpenPartialHomeomorph _ G.splitDeriv (by simp)

def plog (X : G.Mat) : G.Color := (G.coord.symm X).1

private lemma coord_in : (0 : G.Color × G.Normal) ∈ G.coord.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source ..

private lemma coord_out : (1 : G.Mat) ∈ G.coord.target := by
  rw [← G.splitNormal_zero]
  exact ContDiffAt.image_mem_toOpenPartialHomeomorph_target ..

private lemma coord_one : G.coord.symm 1 = 0 := by
  rw [← G.splitNormal_zero]; exact G.coord.left_inv G.coord_in

@[simp] theorem plog_one : G.plog 1 = 0 := by simp [plog,G.coord_one]

theorem plog_diff : ContDiffAt ℝ ω G.plog 1 := by
  have h := G.splitDiff.to_localInverse G.splitDeriv (show ω ≠ (0 : WithTop ℕ∞) by simp)
  rw [G.splitNormal_zero] at h
  exact contDiffAt_fst.comp (1 : G.Mat) h

theorem plog_left : ∀ᶠ x : G.Color in 𝓝 0, G.plog (G.mat (G.lieExp x)) = x := by
  have h := (continuous_id.prodMk (continuous_const (y := (0 : G.Normal)))).tendsto (0:G.Color)
  filter_upwards [h.eventually (G.coord.open_source.mem_nhds G.coord_in)] with x hx
  have hh := G.coord.left_inv hx
  change G.coord.symm (G.splitNormal (x,0)) = _ at hh
  simpa [plog,splitNormal, - mat_lieExp] using congr_arg Prod.fst hh

theorem plog_right : ∀ᶠ X : G.El in 𝓝 1, G.lieExp (G.plog (G.mat X)) = X := by
  have h : Tendsto G.mat (𝓝 1) (𝓝 1) := G.continuous_mat.tendsto _
  have he : Tendsto G.coord.symm (𝓝 1) (𝓝 0) := by
    rw [← G.coord_one]
    exact (G.coord.symm.continuousAt G.coord_out).tendsto
  have hd := (continuous_snd.tendsto (0:G.Color × G.Normal)).comp (he.comp h)
  filter_upwards [hd.eventually G.isolates, h.eventually (G.coord.open_target.mem_nhds G.coord_out)] with u hu hv
  let p := G.coord.symm (G.mat u)
  let x := G.lieExp (G.plog (G.mat u))
  have hg : G.mat x * exp (p.2 : G.Mat) = G.mat u := G.coord.right_inv hv
  have hs : p.2 = 0 := hu ⟨x⁻¹ * u, by rw [G.mat_mul,← hg, ← mul_assoc, ← G.mat_mul, inv_mul_cancel]; simp [p]⟩
  apply G.mat_injective; rwa [hs, Submodule.coe_zero, exp_zero,mul_one] at hg
end YM.Gauge
