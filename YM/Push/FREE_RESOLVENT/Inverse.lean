import YM.Push.FREE_RESOLVENT.Gap

/-!
# Weighted finite-matrix resolvent

Use diagonal weight conjugation with `exp` and a real shift `+ u I`.
Dimension-*independent* pointwise cost: no comparison of l¹
and l² at all sites. The only volume constant paid to conclude Schur
bounds is for summing an exponential of distance with some of the width.
Use the very same threshold for every principal submatrix (every window).

`safeRate` is symbolic schedule data (no M based on the sampled volume
allowed for a uniform application). The shift is not charged in the width.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Matrix
open scoped BigOperators
variable {X ι : Type*}

section tilt
variable [Fintype ι]
/-- Diagonal weight tilt (value at the output divided by that at the input). -/
def tilt (F : ι → ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  of fun i j => Real.exp (F i-F j) * A i j

lemma tilt_mul (F : ι → ℝ) (A B : Matrix ι ι ℝ) : tilt F A * tilt F B = tilt F (A*B) := by
  ext i j; simp only [tilt,Matrix.mul_apply,Matrix.of_apply,Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show F i-F j = (F i-F k)+(F k-F j) by ring, Real.exp_add]; ring

omit [Fintype ι] in
@[simp] lemma tilt_one [DecidableEq ι] (F : ι → ℝ) : tilt F 1 = 1 := by
  ext i j; by_cases i=j <;> simp [*,tilt,Matrix.one_apply]

omit [Fintype ι] in
lemma tilt_shift [DecidableEq ι] (F : ι → ℝ) (A : Matrix ι ι ℝ) (u : ℝ) : tilt F (A + u • 1) = tilt F A + u • 1 := by
  ext i j; by_cases i=j <;> simp [*,tilt,Matrix.one_apply]

-- useful without small-s assumption
lemma exp_move (s : ℝ) : |Real.exp s - 1| ≤ |s| * Real.exp |s| := by
  by_cases h : 0 ≤ s
  · rw [abs_of_nonneg h, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp h))]
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-s)) (Real.exp_pos s).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hh
    linarith
  have ha := Real.add_one_le_exp s
  have he : Real.exp s ≤ 1 := by simpa using Real.exp_monotone (le_of_lt (lt_of_not_ge h))
  rw [abs_of_nonpos (sub_nonpos.mpr he), abs_of_nonpos (le_of_lt (lt_of_not_ge h))]
  have hz : 1 ≤ Real.exp (-s) := Real.one_le_exp (neg_nonneg.mpr (le_of_lt (lt_of_not_ge h)))
  linarith only [ha, mul_le_mul_of_nonneg_left hz (neg_nonneg.mpr (le_of_lt (lt_of_not_ge h)))]

lemma exp_distortion (D : Cost X) (x y : X) {s σ γ : ℝ} (hγ : 0 ≤ γ) (hg : γ < σ)
    (he : |s| ≤ γ * D.d x y) :
    |Real.exp s - 1| ≤ γ * (σ-γ)⁻¹ * D.weight σ x y := by
  have hd := D.nonneg x y
  have hw := sub_pos.mpr hg
  have hb : D.d x y ≤ (σ-γ)⁻¹ * D.weight (σ-γ) x y := by
    rw [inv_mul_eq_div, le_div_iff₀ hw]
    unfold Cost.weight; linarith only [Real.add_one_le_exp ((σ-γ)*D.d x y)]
  calc
    _ ≤ |s| * Real.exp |s| := exp_move _
    _ ≤ (γ * ((σ-γ)⁻¹ * D.weight (σ-γ) x y)) * D.weight γ x y := by
      refine mul_le_mul (he.trans (mul_le_mul_of_nonneg_left hb hγ)) (Real.exp_monotone he)
        (Real.exp_pos _).le (mul_nonneg hγ (mul_nonneg (inv_pos.mpr hw).le (D.weight_pos ..).le))
    _ = _ := by rw [mul_assoc _ _ (D.weight γ _ _), mul_assoc _ _ (D.weight γ _ _),
                      ← D.weight_add, sub_add_cancel]; ring

/-- Schur control of change in quadratic form generator. Only uses the
Lipschitz condition. No sup bound on the conjugators required. -/
lemma tilt_deviation (D : Cost X) (a : ι → X) (F : ι → ℝ)
    {σ γ M : ℝ} {A : Matrix ι ι ℝ} (hγ : 0 ≤ γ) (hg : γ < σ)
    (hF : ∀ i j, |F i - F j| ≤ γ * D.d (a i) (a j)) (hA : D.Schur a a σ M A) :
    D.Schur a a 0 (γ*(σ-γ)⁻¹*M) (tilt F A-A) := by
  let t := γ*(σ-γ)⁻¹
  have ht : 0 ≤ t := mul_nonneg hγ (inv_pos.mpr (sub_pos.mpr hg)).le
  have h (i j : ι) : |(tilt F A-A) i j| ≤ t*(D.weight σ (a i) (a j)*|A i j|) := by
    rw [Matrix.sub_apply, tilt, Matrix.of_apply,
      show Real.exp (F i-F j)*A i j - A i j = (Real.exp (F i-F j)-1)*A i j by ring,
      abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (exp_distortion D _ _ hγ hg (hF i j)) (abs_nonneg _)
  constructor <;> constructor <;> intro i
  · simp only [Cost.weight_zero, one_mul]
    refine le_trans (Finset.sum_le_sum fun j _ => h i j) ?_
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hA.rows.bound i) ht
  simp only [Cost.weight_zero, one_mul, Matrix.transpose_apply]
  apply le_trans (Finset.sum_le_sum fun j _ => h j i)
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ ht
  simpa only [Matrix.transpose_apply,D.weight_symm σ (a i)] using hA.cols.bound i
end tilt

/-- One common tilt exponent; works also for smaller tilt. Assumes (in
uses) positive width and r, nonnegative M. -/
def safeRate (σ M r : ℝ) : ℝ := min (σ/2) (r*σ/(4*(M+1)))
lemma rate_pos {σ M r : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (hr : 0 < r) :
    0 < safeRate σ M r := lt_min (half_pos hσ) (by positivity)
lemma rate_lt {σ M r : ℝ} (hσ : 0 < σ) : safeRate σ M r < σ :=
  lt_of_le_of_lt (min_le_left ..) (half_lt_self hσ)
lemma rate_safe {σ M r γ : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (hr : 0 ≤ r) (hγ : 0 ≤ γ)
    (hg : γ ≤ safeRate σ M r) : γ*(σ-γ)⁻¹*M ≤ r/2 := by
  have hh := hg.trans (min_le_left .. : safeRate σ M r ≤ σ/2)
  have hw : 0 < σ-γ := sub_pos.mpr (hg.trans_lt (rate_lt hσ))
  have hl := (le_div_iff₀ (show 0 < 4*(M+1) by positivity)).mp (hg.trans (min_le_right ..))
  rw [show γ*(σ-γ)⁻¹*M = (γ*M)/(σ-γ) by ring, div_le_iff₀ hw]
  nlinarith only [hγ, mul_le_mul_of_nonneg_right hh hr, hl]

variable [Fintype ι] [DecidableEq ι]
/-- Total (check invertibility hypotheses for conclusions). -/
def resolve (A : Matrix ι ι ℝ) (u : ℝ) := (A + u • 1)⁻¹

lemma resolve_right {A : Matrix ι ι ℝ} {r u : ℝ} (h : Gap A r) (hr : 0 < r) (hu : 0 ≤ u) :
    (A+u • 1) * resolve A u = 1 := Matrix.mul_nonsing_inv _ ((h.shift u).unit_det (by linarith))
lemma resolve_left {A : Matrix ι ι ℝ} {r u : ℝ} (h : Gap A r) (hr : 0 < r) (hu : 0 ≤ u) :
    resolve A u * (A+u • 1) = 1 := Matrix.nonsing_inv_mul _ ((h.shift u).unit_det (by linarith))

/-- Same constants for any cardinality/admissible masks. -/
theorem resolve_point {A : Matrix ι ι ℝ} {D : Cost X} {a : ι → X} {σ M r u γ : ℝ}
    (hM : 0 ≤ M) (hσ : 0 < σ) (h : D.Schur a a σ M A) (hw : Gap A r)
    (hr : 0 < r) (hu : 0 ≤ u) (hγ : 0 ≤ γ) (hg : γ ≤ safeRate σ M r) (i j : ι) :
    |resolve A u i j| ≤ D.weight (-γ) (a i) (a j) * (r/2+u)⁻¹ := by
  let F (k : ι) := γ*D.d (a k) (a j)
  have hh := tilt_deviation D a F hγ (hg.trans_lt (rate_lt hσ)) (fun x y => by
    unfold F; rw [← mul_sub, abs_mul, abs_of_nonneg hγ]
    refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨?_,?_⟩) hγ
    · rw [D.comm (a x) (a y)]; linarith only [D.triangle (a y) (a x) (a j)]
    linarith only [D.triangle (a x) (a y) (a j)]) h
  have hj : Gap (tilt F (A+u • 1)) (r/2+u) := by
    rw [tilt_shift]
    exact ((hw.perturb hh).mono (by linarith only [rate_safe hσ hM hr.le hγ hg])).shift u
  have H := hj.point (by linarith) (B := tilt F (resolve A u)) (by rw [tilt_mul, resolve_right hw hr hu, tilt_one]) i j
  rw [Cost.weight_neg, inv_mul_eq_div, le_div_iff₀ (D.weight_pos ..), mul_comm]
  simpa only [Cost.weight,tilt,Matrix.of_apply,F,D.self,mul_zero,sub_zero,abs_mul,abs_of_pos (Real.exp_pos _)] using H

theorem resolve_schur {A : Matrix ι ι ℝ} {D : Cost X} {a : ι → X} {σ M r u γ V : ℝ}
    (hM : 0 ≤ M) (hσ : 0 < σ) (h : D.Schur a a σ M A) (hw : Gap A r)
    (hr : 0 < r) (hu : 0 ≤ u) (hv : D.Volume a (safeRate σ M r-γ) V) :
    D.Schur a a γ (V*(r/2+u)⁻¹) (resolve A u) :=
  Cost.Schur.of_point (by positivity) (resolve_point hM hσ h hw hr hu (rate_pos hσ hM hr).le le_rfl) hv hv

lemma uniform_shift (r u : ℝ) (hr : 0 < r) (hu : 0 ≤ u) :
    (r/2+u)⁻¹ ≤ (min (r/2) 1)⁻¹ * (1+u)⁻¹ := by
  rw [mul_comm, ← _root_.mul_inv_rev]
  apply inv_anti₀ (mul_pos (lt_min (half_pos hr) zero_lt_one) (by linarith))
  rw [mul_add, mul_one]
  exact add_le_add (min_le_left ..) (mul_le_of_le_one_left hu (min_le_right ..))

lemma resolve_diff {A B : Matrix ι ι ℝ} {u : ℝ}
    (h : IsUnit (A+u • 1).det) (g : IsUnit (B+u • 1).det) :
    resolve B u - resolve A u = resolve B u * (A-B) * resolve A u := by
  rw [show A-B = (A+u • 1)-(B+u • 1) by abel, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc, show (A+u • 1)*resolve A u = 1 from Matrix.mul_nonsing_inv _ h,
      show resolve B u*(B+u • 1) = 1 from Matrix.nonsing_inv_mul _ g]
  simp



end YM.FreeResolvent
