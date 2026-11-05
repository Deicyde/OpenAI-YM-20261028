import YM.Analysis.Homogeneous
import YM.Bid.Source

/-!
# Real analytic germ of link transport in truncated radial connection data

We use the integral equation in continuous matrix paths (sup norm). Locally
in `Snap` the linear Volterra operator has small norm, so that the actual given
`Hol` agrees with an analytic resolvent expression. This is used link by link;
no assertion of uniform analytic radii over an infinite stencil.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.G02
open Filter Function Set RG Wilson Lattice Labels Source Source.Drops InnerProductSpace MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators

section Operators

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Bounded integration operator with base point zero. `projIcc` extends the
integrand for notation; only values in the unit interval are used. -/
private def primitive [CompleteSpace Y] : C(unitInterval, Y) →L[ℝ] C(unitInterval, Y) := by
  let π := projIcc (0 : ℝ) 1 zero_le_one
  have hint (U : C(unitInterval, Y)) (a b : ℝ) :
      IntervalIntegrable (fun s => U (π s)) volume a b :=
    (U.continuous.comp continuous_projIcc).intervalIntegrable a b
  let L : C(unitInterval, Y) →ₗ[ℝ] C(unitInterval, Y) := {
    toFun U := ⟨fun t => ∫ s in 0..(t : ℝ), U (π s),
      (intervalIntegral.continuous_primitive (hint U) 0).comp continuous_subtype_val⟩
    map_add' U W := ContinuousMap.ext fun t => intervalIntegral.integral_add
      (hint U 0 (t : ℝ)) (hint W 0 (t : ℝ))
    map_smul' r U := ContinuousMap.ext fun t => by
      change (∫ s in 0..(t : ℝ), r • U (π s)) = r • ∫ s in 0..(t : ℝ), U (π s)
      rw [intervalIntegral.integral_smul] }
  refine L.mkContinuous 1 fun U => ?_
  rw [one_mul]
  refine (ContinuousMap.norm_le (L U) (norm_nonneg U)).2 fun t => ?_
  change ‖∫ s in 0..(t : ℝ), U (π s)‖ ≤ ‖U‖
  calc
    _ ≤ ‖U‖ * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => U.norm_coe_le_norm (π s)
    _ ≤ ‖U‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg U) t.property.2

/-- At zero a parameter-linear family of bounded operators implies analyticity of
solutions (germ) to `F(x) = a + T(x)(F(x))`. Differentiate the equation. -/
private theorem fixedGerm [CompleteSpace Y] (T : X →L[ℝ] Y →L[ℝ] Y)
    (F : X → Y) (a : Y) (h : ∀ x, F x = a + T x (F x)) :
    AnalyticAt ℝ F 0 ∧ F 0 = a ∧ HasFDerivAt F (T.flip a) 0 := by
  have hz : F 0 = a := by simpa using h 0
  have H : AnalyticAt ℝ F 0 := by
    have hi : AnalyticAt ℝ (fun B : Y →L[ℝ] Y => Ring.inverse (1 - B)) (T 0) := by
      rw [map_zero]
      exact analyticAt_inverse_one_sub ℝ _
    apply AnalyticAt.congr (((ContinuousLinearMap.apply ℝ Y a).analyticAt _).comp
      (hi.comp (T.analyticAt _)))
    have ht : Tendsto T (𝓝 0) (𝓝 0) := by simpa using T.continuous.tendsto 0
    filter_upwards [ht.eventually (Metric.ball_mem_nhds 0 one_pos)] with x hx
    have hu : IsUnit (1 - T x) :=
      isUnit_one_sub_of_norm_lt_one (show ‖T x‖ < 1 by simpa using hx)
    have ha : (1 - T x) (F x) = a := by
      change F x - T x (F x) = a
      exact sub_eq_iff_eq_add.mpr (h x)
    change Ring.inverse (1 - T x) a = F x
    rw [← ha, ← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hu,
      one_apply_eq_self]
  have hD := (hasFDerivAt_const a (0 : X)).add
    (T.hasFDerivAt.clm_apply H.differentiableAt.hasFDerivAt)
  refine ⟨H, hz, ?_⟩
  have he : (fun x => a + T x (F x)) = F := funext fun x => (h x).symm
  simpa [Pi.add_def, he, hz] using hD

/-- Restrict `f` to a line through the origin (for identifying `fderiv`). -/
private theorem onRay {f : X → Y} {L : X →L[ℝ] Y} (h : HasFDerivAt f L 0) (J : X) :
    HasDerivAt (fun t : ℝ => f (t • J)) (L J) 0 := by
  have hd : HasDerivAt (fun t : ℝ => t • J) J 0 := by
    simpa using! (hasDerivAt_id' (0 : ℝ)).smul_const J
  exact h.comp_hasDerivAt_of_eq 0 hd (by simp)

/-- Endpoint of the right-multiplication ODE, for a coefficient field `A`
linear in some finite-dimensional parameters. No dependence regularity is
assumed on the given solutions `u`. -/
theorem endpointGerm {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    [FiniteDimensional ℝ X]
    (A : X →ₗ[ℝ] ℝ → R) (hA : ∀ x : X, Continuous (A x))
    (u : X → ℝ → R) (hu : ∀ x, u x 0 = 1)
    (hode : ∀ x t, HasDerivAt (u x) (u x t * A x t) t) :
    AnalyticAt ℝ (fun x : X => u x 1) 0 ∧ u 0 1 = 1 ∧
      ∀ x : X, HasDerivAt (fun t : ℝ => u (t • x) 1) (∫ s in (0 : ℝ)..1, A x s) 0 := by
  let B : X →ₗ[ℝ] C(unitInterval, R) := {
    toFun x := ⟨fun t => A x t.val, (hA x).comp continuous_subtype_val⟩
    map_add' x y := ContinuousMap.ext fun t => congr_fun (A.map_add x y) (t : ℝ)
    map_smul' r x := ContinuousMap.ext fun t => congr_fun (A.map_smul r x) (t : ℝ) }
  let T : X →L[ℝ] C(unitInterval, R) →L[ℝ] C(unitInterval, R) :=
    ((ContinuousLinearMap.compL ℝ C(unitInterval, R) _ _)
      (primitive (Y := R))).comp
        ((ContinuousLinearMap.mul ℝ C(unitInterval, R)).flip.comp B.toContinuousLinearMap)
  have hcont (x : X) : Continuous (u x) := continuous_iff_continuousAt.2
    fun t => (hode x t).continuousAt
  let F (x : X) : C(unitInterval, R) := ⟨fun t => u x t.val,
    (hcont x).comp continuous_subtype_val⟩
  let π := projIcc (0 : ℝ) 1 zero_le_one
  have hp (t : unitInterval) (s : ℝ) (hs : s ∈ uIcc 0 (t : ℝ)) : (π s).val = s := by
    rw [uIcc_of_le t.property.1] at hs
    unfold π
    rw [projIcc_of_mem _ (show s ∈ unitInterval from ⟨hs.1, hs.2.trans t.property.2⟩)]
  have he (x : X) : F x = 1 + T x (F x) := by
    refine ContinuousMap.ext fun t => ?_
    change u x (t : ℝ) = 1 + ∫ s in 0..(t : ℝ), u x (π s).val * A x (π s).val
    rw [intervalIntegral.integral_congr
      (show EqOn (fun s => u x (π s).val * A x (π s).val) (fun s => u x s * A x s)
        (uIcc 0 (t : ℝ)) from fun s hs => by
          change u x (π s).val * A x (π s).val = _
          rw [hp t s hs]),
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hode x s) (((hcont x).mul (hA x)).intervalIntegrable _ _), hu x]
    abel
  obtain ⟨ha, hz, hd⟩ := fixedGerm T F 1 he
  let V : C(unitInterval, R) →L[ℝ] R := ContinuousMap.evalCLM ℝ (1 : unitInterval)
  refine ⟨(V.analyticAt _).comp ha, congr_arg V hz, fun x => ?_⟩
  apply (onRay (V.hasFDerivAt.comp 0 hd) x).congr_deriv
  change (∫ s in 0..(1 : ℝ), (1 : R) * A x (π s).val) = _
  exact intervalIntegral.integral_congr (fun s hs => by
    rw [hp 1 s hs, one_mul])

end Operators

section Link
variable {G : Gauge}

/-- Specialize to the positive link at scaling parameter one. The derivative
along an arbitrary direction of radial data is the integral with a **plus**
sign, and in the Lie subspace with the specified color scaling. -/
theorem linkGerm (H : Hol G) (d : ℕ) (p : Edge Cover) :
    AnalyticAt ℝ (fun J : Snap G d => G.mat (H.links d (expand d J) 1 p)) 0 ∧
    H.links d (expand d 0) 1 p = 1 ∧
    ∀ J : Snap G d, HasDerivAt (fun t : ℝ => G.mat (H.links d (expand d (t • J)) 1 p))
      (G.colorMat (access J p)) 0 := by
  have hc (J : Snap G d) : Continuous (partConnection d (expand d J) 1 p) := by
    unfold partConnection
    simp only [potential, one_smul]
    refine continuous_finsetSum _ fun j _ => ?_
    exact (Tensor.diag_smooth _ 1).continuous.comp (by fun_prop)
  let A : Snap G d →ₗ[ℝ] ℝ → G.Mat := {
    toFun J t := G.colorMat (partConnection d (expand d J) 1 p t)
    map_add' J K := by
      funext t
      change G.colorMat _ = G.colorMat _ + G.colorMat _
      rw [← map_add]
      congr 1
      simp only [partConnection, potential, one_smul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Taylor.value, Tensor.diagonal, expand, dif_pos (Finset.mem_range.mp hj)]
      rfl
    map_smul' r J := by
      funext t
      change G.colorMat _ = r • G.colorMat _
      rw [← map_smul]
      congr 1
      simp only [partConnection, potential, one_smul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Taylor.value, Tensor.diagonal, expand, dif_pos (Finset.mem_range.mp hj)]
      rfl }
  obtain ⟨ha, hz, hJ⟩ := endpointGerm A
    (fun J => G.colorMat.continuous_of_finiteDimensional.comp (hc J))
    (fun J t => G.mat (H.flow d (expand d J) 1 p t))
    (fun J => by rw [(H.solves ..).1, G.mat_one])
    (fun J t => (H.solves d (expand d J) 1 p).2 t)
  refine ⟨ha, G.mat_injective (hz.trans G.mat_one.symm), fun J => (hJ J).congr_deriv ?_⟩
  exact G.colorMat.toContinuousLinearMap.intervalIntegral_comp_comm
    ((hc J).intervalIntegrable _ _)

end Link

section Walk
variable {G : Gauge}

private theorem matStarGerm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : X → G.Mat} (h : AnalyticAt ℝ F 0) : AnalyticAt ℝ (fun J => star (F J)) 0 :=
  (((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap).analyticAt _).comp h

/-- The same calculation as `Exterior.curvature_linear` for exponential
increments, but here for the actual cover links whose tangents `linkGerm`
gives. -/
theorem walkGerm (H : Hol G) (d : ℕ) (w : Walk) (x : Cover) :
    AnalyticAt ℝ (fun J : Snap G d => G.mat (travel (H.links d (expand d J) 1) x w)) 0 ∧
    ∀ J : Snap G d,
      HasDerivAt (fun t : ℝ => G.mat (travel (H.links d (expand d (t • J)) 1) x w))
        (G.colorMat (Exterior.linkSum (access J) x w)) 0 := by
  have hz : H.links d (expand d 0) 1 = 1 := funext fun p => (linkGerm H d p).2.1
  induction w generalizing x with
  | nil =>
    simp only [travel, Exterior.linkSum, map_zero]
    exact ⟨analyticAt_const, fun _ => hasDerivAt_const _ _⟩
  | cons l w ih =>
    have ha : AnalyticAt ℝ (fun J : Snap G d => G.mat (l.read (H.links d (expand d J) 1) x)) 0 := by
      unfold Step.read
      split
      · simp only [G.mat_inv]
        exact matStarGerm (linkGerm H d _).1
      · exact (linkGerm H d _).1
    obtain ⟨hb, hd⟩ := ih (x + l.vec)
    constructor
    · simp_rw [travel, G.mat_mul]
      exact ha.mul hb
    intro J
    have hh : HasDerivAt (fun t : ℝ => G.mat (l.read (H.links d (expand d (t • J)) 1) x))
        (G.colorMat (if l.neg then -access J (l.used x) else access J (l.used x))) 0 := by
      unfold Step.read
      split
      · rw [map_neg, ← G.colorMat_skew]
        simp only [G.mat_inv]
        exact ((linkGerm H d (l.used x)).2.2 J).star
      · exact (linkGerm H d _).2.2 J
    simp_rw [travel, G.mat_mul]
    apply (hh.mul (hd J)).congr_deriv
    simp only [zero_smul, hz, Pressure.one,
      show l.read (1 : CoverConfig G) x = 1 from by simp [Step.read],
      G.mat_one, mul_one, one_mul, Exterior.linkSum, map_add]

/-- Compute `initial` without any symmetry hypothesis. Conjugating the small
face loop by the walk realizes `Slot.eval`; the connector contributions
cancel in its differential. -/
theorem slotGerm (H : Hol G) (d : ℕ) (v : Slot) :
    AnalyticAt ℝ (takes H d v) 0 ∧ ∀ J, Blurb H d v J = glow J v := by
  let U (J : Snap G d) := H.links d (expand d J) 1
  let Z (J : Snap G d) := travel (U J) 0 v.walk
  let w := square v.plaq.val.1 v.plaq.val.2
  let Y (J : Snap G d) := faceValue (U J) (v.offset, v.plaq)
  let B (J : Snap G d) := Z J * Y J * (Z J)⁻¹
  have haz : AnalyticAt ℝ (fun J => G.mat (Z J)) 0 := (walkGerm H d v.walk 0).1
  have hay : AnalyticAt ℝ (fun J => G.mat (Y J)) 0 := (walkGerm H d w v.offset).1
  have hab : AnalyticAt ℝ (fun J => G.mat (B J)) 0 := by
    simp only [B, G.mat_mul, G.mat_inv]
    exact (haz.mul hay).mul (matStarGerm haz)
  have he (J) : takes H d v J =
      G.projectColor ((1/2 : ℝ) • (G.mat (B J) - star (G.mat (B J)))) :=
    (G.curvature_conjugate (Z J) (Y J)).symm
  have ha : AnalyticAt ℝ (takes H d v) 0 := by
    rw [funext he]
    have hf : AnalyticAt ℝ (fun J => (1/2 : ℝ) • (G.mat (B J) - star (G.mat (B J)))) 0 :=
      (hab.sub (matStarGerm hab)).const_smul (c := (1/2 : ℝ))
    exact (G.projectColor.toContinuousLinearMap.analyticAt _).comp hf
  refine ⟨ha, fun J => ?_⟩
  have hu : U 0 = 1 := funext fun i => (linkGerm H d i).2.1
  have hz : Z 0 = 1 := by dsimp only [Z]; rw [hu]; exact Pressure.one _
  have hy : Y 0 = 1 := by dsimp only [Y]; rw [hu]; exact Pressure.one _
  let z := G.colorMat (Exterior.linkSum (access J) 0 v.walk)
  let y := G.colorMat (glow J v)
  have dz : HasDerivAt (fun t : ℝ => G.mat (Z (t • J))) z 0 := (walkGerm H d v.walk 0).2 J
  have dy : HasDerivAt (fun t : ℝ => G.mat (Y (t • J))) y 0 := (walkGerm H d w v.offset).2 J
  have db : HasDerivAt (fun t : ℝ => G.mat (B (t • J))) y 0 := by
    simp only [B, G.mat_mul, G.mat_inv]
    apply ((dz.mul dy).mul dz.star).congr_deriv
    simp only [Pi.mul_apply, zero_smul, hz, hy, G.mat_one, mul_one, one_mul, star_one,
      show star z = -z from G.colorMat_skew _]
    abel
  have ht : HasDerivAt (fun t : ℝ => (1/2 : ℝ) •
      (G.mat (B (t • J)) - star (G.mat (B (t • J))))) y 0 := by
    apply ((db.sub db.star).const_smul (1/2 : ℝ)).congr_deriv
    rw [show star y = -y from G.colorMat_skew _, sub_neg_eq_add, ← two_smul ℝ,
      smul_smul, div_mul_cancel₀ _ (two_ne_zero' ℝ), one_smul]
  have h : HasDerivAt (fun t : ℝ => takes H d v (t • J)) (glow J v) 0 := by
    simp_rw [he]
    apply (G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 ht).congr_deriv
    exact G.project_colorMat _
  exact (onRay ha.differentiableAt.hasFDerivAt J).unique h
end Walk

theorem answer : YM.Bid.G02 := by
  intro h G H d
  exact ⟨fun v => (slotGerm H d v).1, (h G H).2 d, fun J v => (slotGerm H d v).2 J⟩

end YM.Work.G02
