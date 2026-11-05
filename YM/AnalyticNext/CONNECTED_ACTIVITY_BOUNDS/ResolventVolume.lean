import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.PSeries
import YM.Next.BOUNDARY.Coordinates
import YM.Next.EXTRACTION.Tails
import YM.Next.SCHEDULE.Blocks

/-!
# Finite volume bills for the selected Gaussian. Part 1: An interpolation
invoice for log determinant of **real** physical matrices

E (6259–6571, 6979), determinant part. We'll use a compact parameter for
estimating/varying the normalization and producing the determinant letters
instead of evaluating the individual integrals out to infinity. Use over the
actual, fixed physical torus with full Gram and again on windows, prior to any
connectivity expansion. Doesn't require nonempty index sets (pivot tests would
have to see to that). Nothing thermodynamic. In particular no statement about
differentiating across a change of a physical sector/projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.ResolventVolume
open Function Matrix MeasureTheory
open scoped BigOperators Topology Matrix.Norms.Frobenius
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coordinates are all the real entries separately. -/
lemma hasDerivAt_det {f : ℝ → Matrix n n ℝ} {B : Matrix n n ℝ} {t : ℝ}
    (h : (f t).det ≠ 0) (g : ∀ i j, HasDerivAt (fun x => f x i j) (B i j) t) :
    HasDerivAt (fun x => (f x).det) (trace ((f t)⁻¹ * B) * (f t).det) t := by
  let V := f t
  let D : ContinuousMultilinearMap ℝ (fun _ : n => n → ℝ) ℝ :=
    { Matrix.detRowAlternating.toMultilinearMap with
      cont := by
        change Continuous fun A : n → n → ℝ => (Matrix.of A).det
        refine (continuous_matrix ?_).matrix_det
        intro i j
        simp only [of_apply]; fun_prop }
  have he : HasDerivAt (fun x (i j : n) => f x i j) (fun i j => B i j) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => g i j
  let G := B * V⁻¹
  have hh : G * V = B := by
    unfold G; rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.mpr h), Matrix.mul_one]
  have hu (i : n) : Matrix.det (V.updateRow i (B i)) = G i i * V.det := by
    have H : (∑ k, G i k • V k) = B i := by
      funext m
      nth_rewrite 1 [Finset.sum_apply]; exact congr_fun (congr_fun hh i) m
    rw [← H]; exact Matrix.det_updateRow_sum ..
  have hx := (D.hasFDerivAt _).comp_hasDerivAt t he
  rw [ContinuousMultilinearMap.linearDeriv_apply] at hx
  rw [Matrix.trace_mul_comm, Matrix.trace, Finset.sum_mul]
  change HasDerivAt (fun x => (f x).det) (∑ i, G i i * V.det) t
  change HasDerivAt (fun x => (f x).det) (∑ i, Matrix.det (V.updateRow i (B i))) t at hx
  simpa only [hu] using hx

lemma hasDerivAt_log_det {f : ℝ → Matrix n n ℝ} {B : Matrix n n ℝ} {t : ℝ}
    (h : (f t).det ≠ 0) (g : ∀ i j, HasDerivAt (fun x => f x i j) (B i j) t) :
    HasDerivAt (fun x => Real.log (f x).det) (trace ((f t)⁻¹ * B)) t := by
  simpa only [mul_div_cancel_right₀ _ h] using! (hasDerivAt_det h g).log h

/-- Real physical scalar/spectral interpolation used in chains. -/
def graph (A H : Matrix n n ℝ) (t : ℝ) := A + t • H

lemma inv_continuous {α : Type*} [TopologicalSpace α] {s : Set α} {F : α → Matrix n n ℝ}
    (hf : ContinuousOn F s) (he : ∀ x ∈ s, (F x).det ≠ 0) : ContinuousOn (fun x => (F x)⁻¹) s := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv]
  have h1 : Continuous fun x : Matrix n n ℝ => x.det := continuous_id.matrix_det
  have h2 : Continuous fun x : Matrix n n ℝ => x.adjugate := continuous_id.matrix_adjugate
  exact ((h1.comp_continuousOn hf).inv₀ he).smul (h2.comp_continuousOn hf)

omit [Fintype n] [DecidableEq n] in
lemma graph_differentiates (A H : Matrix n n ℝ) (i j : n) (t : ℝ) :
    HasDerivAt (fun x => graph A H x i j) (H i j) t := by
  have h := ((hasDerivAt_id' t).mul_const (H i j)).const_add (A i j)
  simpa only [graph, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_mul] using h

omit [Fintype n] [DecidableEq n] in
lemma graph_continuous (A H : Matrix n n ℝ) : Continuous (graph A H) := by
  unfold graph; fun_prop

lemma graph_inverse (A H : Matrix n n ℝ) (h : ∀ x ∈ Set.Icc (0:ℝ) 1, (graph A H x).det ≠ 0) :
    ContinuousOn (fun x => (graph A H x)⁻¹) (Set.uIcc 0 1) := by
  rw [Set.uIcc_of_le zero_le_one]; exact inv_continuous (graph_continuous ..).continuousOn h

/-- The actual log det bill. Will use also for `C` normalization, not a new
choice after expansion; and for quadratic tilts of the SAME Gaussian on the
Z coordinates. Form permits a nonsymmetric matrix in the `AC-I` letters. -/
theorem invoice (A H : Matrix n n ℝ) (h : ∀ x ∈ Set.Icc (0:ℝ) 1, (graph A H x).det ≠ 0) :
    (∫ t in (0:ℝ)..1, Matrix.trace ((graph A H t)⁻¹ * H)) = Real.log (A + H).det - Real.log A.det := by
  have hi : ContinuousOn (fun x => trace ((graph A H x)⁻¹ * H)) (Set.uIcc (0:ℝ) 1) :=
    (show Continuous fun x : Matrix n n ℝ => trace x from continuous_id.matrix_trace).comp_continuousOn
      ((graph_inverse A H h).mul continuousOn_const)
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1) (f:=fun x => Real.log (graph A H x).det)
    (fun x hx => hasDerivAt_log_det (h x (by simpa only [Set.uIcc_of_le zero_le_one] using hx))
      (fun i j => graph_differentiates A H i j x)) hi.intervalIntegrable
  simpa only [graph, one_smul, zero_smul, add_zero] using hp
end YM.AnalyticNext.ConnectedActivity.ResolventVolume
