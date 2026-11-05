import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import YM.Analysis.Polydisc
import YM.Pressure.Seeds


/-!
# Real trace-log variations 

Frobenius norm on positions. Mixed derivative, not the quadratic Taylor half.
These lemmas don't assert any gap or field analytic estimate. We keep zero-size
matrices allowed in the differentiation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Filter Function Polynomial
open scoped Topology ContDiff Matrix.Norms.Frobenius

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma det_contDiff : ContDiff ℝ ω (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  change ContDiff ℝ ω (fun X : Matrix ι ι ℝ => Matrix.det X)
  simp_rw [Matrix.det_apply]
  refine ContDiff.sum (fun σ _ => ContDiff.const_smul _ (contDiff_prod ?_))
  intro i _
  let ev : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun m => m (σ i) i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact ev.toContinuousLinearMap.contDiff

private lemma det_one_line (M : Matrix ι ι ℝ) :
    HasDerivAt (fun x : ℝ => (1 + x • M).det) M.trace 0 := by
  rw [← Matrix.derivative_det_one_add_X_smul]
  convert! Polynomial.hasDerivAt (1 + Polynomial.X • M.map ⇑Polynomial.C).det 0 using 1
  ext x
  let φ := evalRingHom x
  change _ = φ (1 + Polynomial.X • M.map ⇑Polynomial.C).det
  rw [RingHom.map_det, map_add, map_one]
  congr 2
  ext i j
  change _ = φ (Polynomial.X * C (M i j))
  simp [φ,smul_eq_mul]; ring

lemma det_variation (M : Matrix ι ι ℝ) (h : IsUnit M.det) (U : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det M U = M.det * (M⁻¹ * U).trace := by
  have hr := (det_one_line (M⁻¹ * U)).const_mul M.det
  simp_rw [← det_mul, Matrix.mul_add, mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
    M.mul_nonsing_inv h, one_mul] at hr
  have hi : HasDerivAt (fun t : ℝ => M + t • U) U 0 := by
    exact HasDerivAt.const_add M (by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const U)
  have hf := ((det_contDiff.differentiable (by simp)) (M + (0:ℝ) • U)).hasFDerivAt.comp_hasDerivAt
    (0:ℝ) hi
  simpa using! (hf.unique hr)

lemma logdet_contDiff {X : E → Matrix ι ι ℝ} {x : E}
    (hx : ContDiffAt ℝ ω X x) (hu : IsUnit (X x).det) :
    ContDiffAt ℝ ω (fun y => Real.log (X y).det) x :=
  ((Real.contDiffAt_log).mpr hu.ne_zero).comp (f := fun y => (X y).det) x (det_contDiff.contDiffAt.comp x hx)

lemma logdet_variation {X : E → Matrix ι ι ℝ} {x : E}
    (hx : DifferentiableAt ℝ X x) (hu : IsUnit (X x).det) (u : E) :
    fderiv ℝ (fun y => Real.log (X y).det) x u = ((X x)⁻¹ * fderiv ℝ X x u).trace := by
  change fderiv ℝ (Real.log ∘ (Matrix.det ∘ X)) x u = _
  have hd := (det_contDiff (ι:=ι)).differentiable (by simp)
  rw [fderiv_comp x (Real.differentiableAt_log hu.ne_zero) ((hd _).comp x hx),
      fderiv_comp x (hd _) hx, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  erw [det_variation _ hu, (Real.hasDerivAt_log hu.ne_zero).hasFDerivAt.fderiv]
  change (X x).det * _ * (X x).det⁻¹ = _
  field_simp [hu.ne_zero]
  rfl

lemma inv_contDiffAt (M : Matrix ι ι ℝ) (h : IsUnit M.det) :
    ContDiffAt ℝ ω (fun X : Matrix ι ι ℝ => X⁻¹) M := by
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  obtain ⟨a,rfl⟩ := M.isUnit_iff_isUnit_det.mpr h
  exact contDiffAt_ringInverse ℝ a

lemma inv_variation (M : Matrix ι ι ℝ) (h : IsUnit M.det) (U : Matrix ι ι ℝ) :
    fderiv ℝ (fun X : Matrix ι ι ℝ => X⁻¹) M U = -(M⁻¹ * U * M⁻¹) := by
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  obtain ⟨a,rfl⟩ := M.isUnit_iff_isUnit_det.mpr h
  have he := congr_arg (fun f : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ => f U) (hasFDerivAt_ringInverse (𝕜:=ℝ) a).fderiv
  rw [Ring.inverse_unit]
  exact he

def traceFee (M M₁ M₂ M₁₂ : Matrix ι ι ℝ) :=
  (M⁻¹ * M₁₂).trace - (M⁻¹ * M₁ * M⁻¹ * M₂).trace

lemma logdet_mixed {X : E → Matrix ι ι ℝ} {x : E} (hx : ContDiffAt ℝ ω X x) (hu : IsUnit (X x).det)
    (v w : E) : iteratedFDeriv ℝ 2 (fun y => Real.log (X y).det) x ![v,w] =
      traceFee (X x) (fderiv ℝ X x v) (fderiv ℝ X x w) (iteratedFDeriv ℝ 2 X x ![v,w]) := by
  let Y y := Real.log (X y).det
  let M := X x
  let T := fun x => (X x)⁻¹
  let P := fun x => fderiv ℝ X x w
  have h : (fun y => fderiv ℝ Y y w) =ᶠ[𝓝 x] fun y => (T y * P y).trace := by
    have he := (det_contDiff.contDiffAt.comp x hx).continuousAt.eventually (isOpen_ne.mem_nhds hu.ne_zero)
    filter_upwards [he,hx.eventually (by simp)] with y hy hg
    exact logdet_variation (hg.differentiableAt (by simp)) (isUnit_iff_ne_zero.mpr hy) w
  have ht := ((inv_contDiffAt _ hu).differentiableAt (by simp)).hasFDerivAt.comp x
    (hx.differentiableAt (by simp)).hasFDerivAt
  have hp := ((hx.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  let τ := (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap
  have hh := τ.hasFDerivAt.comp x (ht.mul' hp)
  have H : fderiv ℝ (fun y => (T y * P y).trace) x = _ := hh.fderiv
  have hd := (((logdet_contDiff hx hu).fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  rw [iteratedFDeriv_two_apply]
  change fderiv ℝ (fderiv ℝ Y) x v w = _
  rw [show fderiv ℝ (fderiv ℝ Y) x v w = fderiv ℝ (fun y => fderiv ℝ Y y w) x v by rw [show _ = _ from hd.fderiv]; simp [Y],
    h.fderiv_eq, H]
  simp only [ContinuousLinearMap.comp_zero, zero_add, Function.comp_apply, ContinuousLinearMap.comp_apply,
    _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.flip_apply, traceFee, iteratedFDeriv_two_apply]
  erw [inv_variation _ hu]
  change (_ + -(M⁻¹ * _ * M⁻¹) * _).trace = _
  rw [neg_mul, trace_add, trace_neg]
  rfl
end YM.Push.Loops
