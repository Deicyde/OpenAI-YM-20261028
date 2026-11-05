import Mathlib.Analysis.Analytic.Binomial
import YM.Complex.Columns


/-!
# One analytic branch near a matrix spectral band

In L² operator norm: normalize by a scalar upper bound and take the
binomial series near identity. Evaluate it on Hermitian inputs in band by
unitary diagonalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F07
open Matrix Holder
open scoped BigOperators Matrix.Norms.L2Operator Topology ENNReal NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real-axis pair of bounds in Funds. -/
def Band (X : M ι) (v A : ℝ) :=
  ∀ x : ι → ℂ,
    v*(dotProduct (star x) x).re ≤ (dotProduct (star x) (X*ᵥx)).re ∧
      (dotProduct (star x) (X*ᵥx)).re ≤ A*(dotProduct (star x) x).re

omit [Fintype ι] in
private lemma diagHerm (s : ι → ℝ) : (D s).IsHermitian := by
  unfold D IsHermitian
  rw [diagonal_conjTranspose]; congr 1; ext1 i; simp

lemma unitaryHerm (y : U ι) (s : ι → ℝ) : IsHermitian (y.val * D s * y.valᴴ) := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, (diagHerm s).eq, mul_assoc]

-- uses precisely the conjugate on the FIRST slot
private lemma vecdot_unit (y : U ι) (x w : ι → ℂ) :
    dotProduct (star (y.val *ᵥ x)) (y.val *ᵥ w) = dotProduct (star x) w := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, united, vecMul_one]

lemma unitaryBand (y : U ι) (s : ι → ℝ) (v A : ℝ) :
    Band (y.val * D s * y.valᴴ) v A ↔ ∀ i, v ≤ s i ∧ s i ≤ A := by
  have h (x : ι → ℂ) :
      dotProduct (star (y.val *ᵥ x)) ((y.val * D s * y.valᴴ) *ᵥ (y.val *ᵥ x)) =
      dotProduct (star x) (D s *ᵥ x) := by
    rw [mulVec_mulVec, mul_assoc _ y.valᴴ, united, mul_one, ← mulVec_mulVec, vecdot_unit]
  constructor
  · intro e i
    let x : ι → ℂ := Pi.single i 1
    have hw := e (y.val *ᵥ x)
    rw [h, vecdot_unit] at hw
    simpa [x, D] using hw
  intro e z
  let x := y.valᴴ *ᵥ z
  have hx : y.val *ᵥ x = z := by unfold x; rw [mulVec_mulVec, united', one_mulVec]
  change v*_ ≤ _ ∧ _ ≤ A*_
  rw [← hx, h, vecdot_unit]
  have h1 : (dotProduct (star x) x).re = ∑ i, Complex.normSq (x i) := by
    simp only [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.normSq_apply, Complex.mul_re]
  have h2 : (dotProduct (star x) (D s *ᵥ x)).re = ∑ i, s i * Complex.normSq (x i) := by
    simp only [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mulVec, dotProduct, D, diagonal, Complex.normSq_apply, Complex.mul_re]; ring
  rw [h1,h2, Finset.mul_sum, Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (e i).1 (Complex.normSq_nonneg _),
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (e i).2 (Complex.normSq_nonneg _)⟩

def binInput (m : ℝ) (X : M ι) := ((m⁻¹:ℝ):ℂ) • X - 1

lemma binInput_unitary (m : ℝ) (y : U ι) (s : ι → ℝ) :
    binInput m (y.val * D s * y.valᴴ) = y.val * D (fun i => m⁻¹*s i-1) * y.valᴴ := by
  have H : D (fun i => m⁻¹*s i-1) = ((m⁻¹:ℝ):ℂ) • D s - 1 := by
    ext i j; by_cases h : i=j <;> simp [h, D]
  rw [H, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, united']; rfl

lemma binInput_bound (m : ℝ) {X : M ι} (hh : X.IsHermitian) {v : ℝ} (h : Band X v m)
    (hv : 0 < v) (hm : v ≤ m) : ‖binInput m X‖ ≤ 1 - m⁻¹*v := by
  obtain ⟨y,s,hy⟩ : ∃ (y : U ι) (s : ι → ℝ), X = y.val * D s * y.valᴴ :=
    ⟨hh.eigenvectorUnitary, hh.eigenvalues, Holder.spectral_diag hh⟩
  rw [hy] at h ⊢
  have H := (unitaryBand y s v m).mp h
  let t := D (fun i => m⁻¹ * s i - 1)
  have he : 0 < m := hv.trans_le hm
  have ha {x : ℝ} (hx : x ≤ m) : m⁻¹*x ≤ 1 := by
    rwa [inv_mul_eq_div, div_le_one he]
  have ht : ‖t‖ ≤ 1 - m⁻¹*v := by
    unfold t D
    rw [Matrix.l2_opNorm_diagonal]; apply (pi_norm_le_iff_of_nonneg (sub_nonneg.mpr (ha hm))).2
    intro i
    rw [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (ha (H i).2))]
    linarith only [mul_le_mul_of_nonneg_left (H i).1 (inv_pos.mpr he).le]
  rw [binInput_unitary]
  calc
    _ ≤ ‖y.val * t‖*‖y.valᴴ‖ := norm_mul_le ..
    _ ≤ ‖y.val * t‖ := mul_le_of_le_one_right (norm_nonneg _) (unitary_safe' _)
    _ ≤ ‖y.val‖*‖t‖ := norm_mul_le ..
    _ ≤ ‖t‖ := mul_le_of_le_one_left (norm_nonneg _) (unitary_safe _)
    _ ≤ _ := ht

def binSum (X : M ι) := (binomialSeries (M ι) ((1 / 2 : ℝ) : ℂ)).sum X

lemma binSum_deriv [Nonempty ι] {X : M ι} (h : ‖X‖ < 1) : DifferentiableAt ℂ binSum X := by
  let p := binomialSeries (M ι) ((1 / 2 : ℝ):ℂ)
  have hr : 1 ≤ p.radius := by
    have he : p.radius = (binomialSeries ℂ ((1 / 2 : ℝ):ℂ)).radius := by
      unfold p binomialSeries FormalMultilinearSeries.radius; simp
    rw [he]
    exact binomialSeries_radius_ge_one
  apply ((p.hasFPowerSeriesOnBall (lt_of_lt_of_le zero_lt_one hr)).analyticOnNhd X ?_).differentiableAt
  apply Metric.eball_subset_eball hr
  rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
  simpa

lemma binSum_bound [Nonempty ι] (r : ℝ) (hr : r < 1) : ∃ K : ℝ, ∀ X : M ι, ‖X‖ ≤ r →
    ‖binSum X‖ ≤ K := by
  let s := Metric.closedBall (0 : M ι) r
  let f : M ι → ℝ := fun X => ‖binSum X‖
  have he : ContinuousOn f s := fun X h =>
    (binSum_deriv (lt_of_le_of_lt (show ‖X‖ ≤ r by simpa [s] using h) hr)).continuousAt.norm.continuousWithinAt
  obtain ⟨K,hK⟩ := ((isCompact_closedBall _ _).image_of_continuousOn he).bddAbove
  exact ⟨K, fun X h => hK ⟨X, by simpa [s], rfl⟩⟩

def binRoot (m : ℝ) (X : M ι) := (Real.sqrt m : ℂ) • binSum (binInput m X)

lemma binRoot_deriv [Nonempty ι] (m : ℝ) {X : M ι} (h : ‖binInput m X‖ < 1) :
    DifferentiableAt ℂ (binRoot m) X := by
  refine ((binSum_deriv h).comp (f:=binInput m) X ?_).const_smul (Real.sqrt m : ℂ)
  unfold binInput; fun_prop

lemma binSum_tsum (X : M ι) : binSum X =
    ∑' n, ((Ring.choose (1 / 2 : ℝ) n : ℝ) : ℂ) • X^n := by
  simp only [Complex.ofReal_choose]
  exact FormalMultilinearSeries.ofScalars_sum_eq _ _

-- entrywise conjugation, NOT Hermiticity (includes parameter negation later)
lemma binRoot_conj (m : ℝ) (X : M ι) : binRoot m (X.map star) = (binRoot m X).map star := by
  have h (X : M ι) : X.map star = Xᴴ.transpose := by ext; simp
  have hr (x : ℝ) : star (x:ℂ) = (x:ℂ) := by simp
  simp only [h, binRoot, binSum_tsum, binInput, conjTranspose_smul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_tsum, conjTranspose_pow, hr, transpose_smul, transpose_sub, Matrix.transpose_one,
    transpose_pow, transpose_tsum]

private lemma chooseHalf {t : ℝ} (ht : ‖t‖ < 1) : HasSum
    (fun n => Ring.choose (1 / 2 : ℝ) n * t ^ n) (Real.sqrt (1 + t)) := by
  have h : t ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]; simpa using ht
  have he := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := 1 / 2)).hasSum h
  simpa only [Real.sqrt_eq_rpow, zero_add, binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using he

lemma binSum_on_unitary (t : ι → ℝ) (ht : ∀ i, ‖t i‖ < 1) (y : U ι) :
    binSum (y.val * D t * y.valᴴ) = y.val * D (fun i => Real.sqrt (1 + t i)) * y.valᴴ := by
  let c := Ring.choose (1 / 2 : ℝ)
  let l : (ι → ℝ) →ₗ[ℝ] M ι :=
    { toFun := D
      map_add' := by intro p q; ext i j; by_cases h : i=j <;> simp [h,D]
      map_smul' := by intro a p; ext i j; by_cases h : i=j <;> simp [h,D] }
  have h : HasSum (fun n : ℕ => c n • t^n) (fun i => Real.sqrt (1 + t i)) :=
    Pi.hasSum.mpr (fun i => by simpa [c] using chooseHalf (ht i))
  have hh : HasSum (fun n : ℕ => D (c n • t^n)) (D fun i => Real.sqrt (1 + t i)) :=
    l.toContinuousLinearMap.hasSum h
  rw [binSum_tsum, ← ((hh.mul_left y.val).mul_right y.valᴴ).tsum_eq]
  refine tsum_congr fun n => ?_
  have hm : D (c n • t^n) = (c n : ℂ) • D (t^n) := by ext i j; by_cases h : i=j <;> simp [h,D]
  rw [spectral_power, hm, Matrix.mul_smul, Matrix.smul_mul]

lemma binRoot_on_unitary (m : ℝ) (hm : 0 < m) (s : ι → ℝ) (hs : ∀ i, 0 < s i ∧ s i ≤ m) (y : U ι) :
    binRoot m (y.val * D s * y.valᴴ) = y.val * D (fun i => Real.sqrt (s i)) * y.valᴴ := by
  let t := fun i => m⁻¹*s i-1
  have ht (i) : ‖t i‖ < 1 := by
    have h : m⁻¹*s i ≤ 1 := by rw [inv_mul_eq_div, div_le_one hm]; exact (hs i).2
    unfold t; rw [Real.norm_eq_abs, abs_lt]; have he := mul_pos (inv_pos.mpr hm) (hs i).1; constructor <;> linarith
  have hw (i) : Real.sqrt (1 + t i) = Real.sqrt (s i) / Real.sqrt m := by
    rw [show 1 + t i = s i / m by unfold t; ring, Real.sqrt_div (hs i).1.le]
  have hh : D (fun i => Real.sqrt (s i)) = (Real.sqrt m : ℂ) • D (fun i => Real.sqrt (1+t i)) := by
    ext i j; by_cases h : i=j
    · simp only [h,D,diagonal_apply_eq,Function.comp_apply, Matrix.smul_apply, smul_eq_mul, hw]; push_cast
      have he : (Real.sqrt m : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hm).ne'
      field_simp
    simp [h,D]
  rw [binRoot, binInput_unitary, binSum_on_unitary t ht, hh, Matrix.mul_smul, Matrix.smul_mul]

lemma binRoot_on_band {X : M ι} (hh : X.IsHermitian) {v m B : ℝ} (h : Band X v m)
    (hv : 0 < v) (hm : 0 < m) (hB : Real.sqrt m ≤ B) :
    (binRoot m X).IsHermitian ∧ Band (binRoot m X) (Real.sqrt v) B ∧
    binRoot m X * binRoot m X = X := by
  obtain ⟨y,s,hy⟩ : ∃ (y : U ι) (s : ι → ℝ), X = y.val * D s * y.valᴴ :=
    ⟨hh.eigenvectorUnitary, hh.eigenvalues, Holder.spectral_diag hh⟩
  rw [hy] at h ⊢
  have H := (unitaryBand y s v m).mp h
  let t := fun i => Real.sqrt (s i)
  have ht : t^2 = s := funext fun i => Real.sq_sqrt ((hv.trans_le (H i).1).le)
  rw [binRoot_on_unitary m hm s (fun i => ⟨hv.trans_le (H i).1, (H i).2⟩)]
  refine ⟨unitaryHerm y t, (unitaryBand y t ..).mpr ?_, ?_⟩
  · exact fun i => ⟨Real.sqrt_le_sqrt (H i).1, (Real.sqrt_le_sqrt (H i).2).trans hB⟩
  rw [← sq, spectral_power y t, ht]
end YM.Work.F07
