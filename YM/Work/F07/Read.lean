import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.Laurent.Eval


/-!
# Reading with a narrower strip; realifying the Fourier coefficients
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F07
open Laurent Filter Topology
open scoped BigOperators

variable {α : Type*} [Fintype α]

lemma stripOpen (η : ℝ) : IsOpen (strip (α := α) η) := by
  rw [show strip η = ⋂ i : α, {p : Phase α | |(p i).im| < η} by
    ext p; simp only [Set.mem_iInter, Set.mem_setOf_eq]; rfl]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const

omit [Fintype α] in
lemma stripConvex (η : ℝ) : Convex ℝ (strip (α := α) η) := by
  intro x hx y hy a b ha hb hab i
  have hx' := abs_lt.mp (hx i)
  have hy' := abs_lt.mp (hy i)
  simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_lt]
  rcases eq_or_lt_of_le ha with ha|ha
  · subst a; simp_all
  rcases eq_or_lt_of_le hb with hb|hb
  · subst b; simp_all
  constructor <;> nlinarith

private def modeArg (x : Shift α) : Phase α →L[ℂ] ℂ :=
  Complex.I • ∑ i, (x i : ℂ) • (ContinuousLinearMap.proj (R := ℂ) i : Phase α →L[ℂ] ℂ)

private lemma mode_eq (x : Shift α) (p : Phase α) : mode p x = Complex.exp (modeArg x p) := by
  simp [modeArg, mode, mul_comm]

private lemma modeArg_bound (x : Shift α) : ‖modeArg x‖ ≤ size x := by
  unfold modeArg size
  rw [norm_smul, Complex.norm_I, one_mul, Nat.cast_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h : ‖(ContinuousLinearMap.proj (R := ℂ) i : Phase α →L[ℂ] ℂ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    simpa using (norm_le_pi_norm p i)
  rw [norm_smul]; apply (mul_le_of_le_one_right (norm_nonneg _) h).trans
  rw [Complex.norm_intCast, ← Int.cast_abs]; simp

/-- Differentiability and a uniform derivative budget already paid by the width.
No bound on real parts needed. -/
lemma readDeriv {η σ A : ℝ} {f : On α ℂ} (hf : Width η A f) (hσ : 0 < σ)
    (hη : σ < η) {p : Phase α} (hp : p ∈ strip σ) :
    DifferentiableAt ℂ (read f) p ∧ ‖fderiv ℂ (read f) p‖ ≤ (η-σ)⁻¹*A := by
  let g : Shift α → Phase α → ℂ := fun i q => mode q i * f i
  let d : Shift α → Phase α → Phase α →L[ℂ] ℂ := fun i q => f i • mode q i • modeArg i
  have hg (i q) : HasFDerivAt (g i) (d i q) q := by
    simp only [d, g, mode_eq]
    exact ((modeArg i).hasFDerivAt.cexp).mul_const _
  let money := fun i => Real.exp (η*size i)*‖f i‖
  let u := fun i => (η-σ)⁻¹*money i
  have hm : Summable money := hf.2.1
  have hu : Summable u := hm.mul_left _
  have hd (i q) (hq : q ∈ strip σ) : ‖d i q‖ ≤ u i := by
    have hx : ‖mode q i‖ ≤ Real.exp (σ*size i) := reward q i σ fun a => (hq a).le
    have hy : (size i : ℝ) ≤ (η-σ)⁻¹*Real.exp ((η-σ)*size i) := by
      have he := Real.add_one_le_exp ((η-σ)*(size i : ℝ))
      rw [inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hη)]
      linarith
    simp only [d, norm_smul]
    calc
      _ ≤ ‖f i‖ * (Real.exp (σ*size i) * ((η-σ)⁻¹ * Real.exp ((η-σ)*size i))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hx ((modeArg_bound i).trans hy) (norm_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
      _ = u i := by
        rw [show Real.exp ((η-σ)*size i) = Real.exp (η*size i)/Real.exp (σ*size i) by
          rw [sub_mul, Real.exp_sub]]
        unfold u money
        field_simp
  have h0 : (0 : Phase α) ∈ strip σ := fun i => by simpa using hσ
  have hs0 : Summable fun i => g i (0 : Phase α) := by
    simpa only [g, mode_constant, one_mul] using hf.summable (hσ.trans hη).le
  have he : HasFDerivAt (read f) (∑' i, d i p) p :=
    hasFDerivAt_tsum_of_isPreconnected hu (stripOpen σ) (stripConvex σ).isPreconnected
      (fun i q _ => hg i q) hd h0 hs0 hp
  have hl (i) : ‖d i p‖ ≤ u i := hd i p hp
  have ht := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hl hu
  refine ⟨he.differentiableAt, ?_⟩
  rw [he.fderiv]
  refine (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum hl hu).trans ?_)
  unfold u; rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hf.2.2 (inv_nonneg.mpr (sub_pos.mpr hη).le)

lemma readDiff {η σ A : ℝ} {f : On α ℂ} (hf : Width η A f) (hσ : 0 < σ) (hη : σ < η)
    {p q : Phase α} (hp : p ∈ strip σ) (hq : q ∈ strip σ) :
    ‖read f p - read f q‖ ≤ (η-σ)⁻¹*A*‖p-q‖ :=
  (stripConvex σ).norm_image_sub_le_of_norm_fderiv_le
    (fun _ h => (readDeriv hf hσ hη h).1) (fun _ h => (readDeriv hf hσ hη h).2) hq hp

omit [Fintype α] in
lemma realStrip (η : ℝ) (hη : 0 < η) {p : Phase α} (h : star p = p) : p ∈ strip η := by
  intro i
  have hi : star (p i) = p i := congr_fun h i
  rw [Complex.star_def, Complex.conj_eq_iff_im] at hi
  simpa only [hi, abs_zero]

lemma widthRealPart {η A : ℝ} {f : On α ℂ} (h : Width η A f) : Width η A (fun x => (f x).re) := by
  have he (x) : Real.exp (η*size x)*‖(f x).re‖ ≤ Real.exp (η*size x)*‖f x‖ :=
    mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos _).le
  have hn (x) : 0 ≤ Real.exp (η*size x)*‖(f x).re‖ := by positivity
  have hs := Summable.of_nonneg_of_le hn he h.2.1
  exact ⟨hn, hs, (hs.tsum_le_tsum he h.2.1).trans h.2.2⟩

/-- Coefficientwise real part -- enough to recover a symbol on the real
axis if it has the mode/conjugation symmetry there. -/
lemma readRealPart {η A : ℝ} {f : On α ℂ} (hf : Width η A f) (hη : 0 < η)
    {p : Phase α} (hp : star p = p) :
    read (fun x => ((f x).re : ℂ)) p = (read f p + star (read f (-p))) / 2 := by
  have hs (q : Phase α) (hq : star q = q) : Summable fun i => mode q i • f i :=
    (hf.series q (fun a => (realStrip η hη hq a).le)).2.1.of_norm
  have hq : star (-p) = -p := by rw [star_neg, hp]
  unfold Laurent.read; rw [tsum_star, ← (hs p hp).tsum_add (hs (-p) hq).star, ← tsum_div_const]
  refine tsum_congr fun x => ?_
  have H := mode_adjoint (-p) x
  rw [hq, mode_opposite, mode_inverse, inv_inv] at H
  have h : f x + star (f x) = 2*((f x).re:ℂ) := by
    rw [Complex.star_def, Complex.add_conj]; push_cast; rfl
  simp only [smul_eq_mul, star_mul, mode_inverse, H]
  rw [mul_comm (star (f x)), ← mul_add, h]
  ring
end YM.Work.F07
