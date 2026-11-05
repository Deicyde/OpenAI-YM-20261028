import YM.Work.F06.Cartan

/-!
# Entrywise budgets versus counting quadratic forms
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F06
open Exterior Matrix Finset
open scoped BigOperators

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Keep the same energy convention as the Fourier promises in Craft. -/
def sqLength (x : m → ℂ) : ℝ := (dotProduct (star x) x).re

def pairingRe (A : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :=
  (dotProduct (star x) (A *ᵥ y)).re

lemma sqLength_apply (x : m → ℂ) : sqLength x = ∑ i, ‖x i‖ ^ 2 := by
  simp_rw [sqLength, dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma sqLength_nonneg (x : m → ℂ) : 0 ≤ sqLength x := by rw [sqLength_apply]; positivity

lemma component_sq_le (x : m → ℂ) (i : m) : ‖x i‖ ^ 2 ≤ sqLength x := by
  rw [sqLength_apply]; exact Finset.single_le_sum (fun j _ => sq_nonneg ‖x j‖) (mem_univ i)

lemma component_le_length (x : m → ℂ) (i : m) : ‖x i‖ ≤ Real.sqrt (sqLength x) := by
  rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), Real.sq_sqrt (sqLength_nonneg _)]
  exact component_sq_le x i

lemma sqLength_smul (a : ℂ) (x : m → ℂ) : sqLength (a • x) = ‖a‖ ^ 2 * sqLength x := by
  simp_rw [sqLength_apply, Finset.mul_sum, Pi.smul_apply, norm_smul, mul_pow]

lemma sqLength_add (x y : m → ℂ) :
    sqLength (x + y) ≤ 2 * (sqLength x + sqLength y) := by
  simp_rw [sqLength_apply, Pi.add_apply, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ (‖x i‖ + ‖y i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (x i) (y i)) _
    _ ≤ _ := by nlinarith only [sq_nonneg (‖x i‖ - ‖y i‖)]

lemma pairingRe_gram (A : Matrix m n ℂ) (x : n → ℂ) :
    pairingRe (A.conjTranspose * A) x x = sqLength (A *ᵥ x) := by
  unfold pairingRe sqLength
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec (star x), ← Matrix.star_mulVec]

lemma pairingRe_add (A B : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :
    pairingRe (A + B) x y = pairingRe A x y + pairingRe B x y := by
  rw [pairingRe, Matrix.add_mulVec, dotProduct_add, Complex.add_re, pairingRe, pairingRe]

lemma pairingRe_sub (A B : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :
    pairingRe (A - B) x y = pairingRe A x y - pairingRe B x y := by
  rw [pairingRe, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, pairingRe, pairingRe]

lemma pairingRe_scale (a : ℝ) (A : Matrix m n ℂ) (x : m → ℂ) (y : n → ℂ) :
    pairingRe ((a:ℂ) • A) x y = a * pairingRe A x y := by
  rw [pairingRe, pairingRe, Matrix.smul_mulVec, dotProduct_smul]
  simp

lemma pairingRe_expand (A : Matrix m m ℂ) (x y : m → ℂ) :
    pairingRe A (x+y) (x+y) =
      pairingRe A x x + pairingRe A x y + pairingRe A y x + pairingRe A y y := by
  simp only [pairingRe, Matrix.mulVec_add, star_add, dotProduct_add, add_dotProduct,
    Complex.add_re]; abel

/-- Slightly loose count, to leave denominators manifestly positive. -/
def countCeil (ι : Type*) [Fintype ι] : ℝ := (Fintype.card ι:ℝ)+1

lemma countCeil_pos (ι : Type*) [Fintype ι] : 0 < countCeil ι := by
  unfold countCeil; positivity

lemma pairingRe_bound (A : Matrix m m ℂ) {C : ℝ} (hC : 0 ≤ C) (he : ∀ i j, ‖A i j‖ ≤ C)
    (x y : m → ℂ) :
    |pairingRe A x y| ≤ countCeil m ^ 2 * C * Real.sqrt (sqLength x) * Real.sqrt (sqLength y) := by
  let X := Real.sqrt (sqLength x)
  let Y := Real.sqrt (sqLength y)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  unfold pairingRe
  refine (Complex.abs_re_le_norm _).trans ?_
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  calc
    _ ≤ ∑ i, ‖∑ j, star (x i) * (A i j * y j)‖ := norm_sum_le ..
    _ ≤ ∑ _ : m, ∑ _ : m, X * (C * Y) := by
      refine Finset.sum_le_sum fun i _ => (norm_sum_le ..).trans (Finset.sum_le_sum fun j _ => ?_)
      simp only [Complex.norm_mul, norm_star]
      exact mul_le_mul (component_le_length _ _) (mul_le_mul (he _ _)
        (component_le_length _ _) (norm_nonneg _) hC) (by positivity) hX
    _ = (Fintype.card m : ℝ) ^ 2 * (C * X * Y) := by simp; ring
    _ ≤ countCeil m ^ 2 * (C * X * Y) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by unfold countCeil; linarith) _) (by positivity)
    _ = _ := by dsimp [X,Y]; ring

lemma pairingRe_diag (A : Matrix m m ℂ) {C : ℝ} (hC : 0 ≤ C) (he : ∀ i j, ‖A i j‖ ≤ C)
    (x : m → ℂ) : |pairingRe A x x| ≤ countCeil m ^ 2 * C * sqLength x :=
  (pairingRe_bound A hC he x x).trans_eq (by
    rw [mul_assoc _ (Real.sqrt _) (Real.sqrt _), ← sq, Real.sq_sqrt (sqLength_nonneg x)])

variable {α : Type*} [Fintype α] [LinearOrder α] {r : ℕ}

lemma contraction_price (w : Blade α (r+1) → ℂ) (k : α) :
    sqLength ((left ℂ r k).transpose *ᵥ w) ≤ countCeil (Blade α r) * sqLength w := by
  rw [sqLength_apply]
  calc
    _ ≤ ∑ _ : Blade α r, sqLength w := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [eliminate_transpose w i k]; split
      · rename_i h
        simpa [Complex.norm_mul, parity] using component_sq_le w (addAxis k i h)
      simpa using sqLength_nonneg w
    _ = (Fintype.card (Blade α r):ℝ) * sqLength w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold countCeil; linarith) (sqLength_nonneg _)

/-- An away-from-harmonic completion-of-squares estimate stated for a
possibly oblique splitting. The extra `v/2` also pays for the norm of the
sum, so no orthogonality is needed. -/
def mixPrice (v M : ℝ) := M + 2*M^2/v + v/2

lemma pairingRe_complete (A : Matrix m m ℂ) {C v L D : ℝ} (hC : 0 ≤ C) (hv : 0 < v)
    (he : ∀ i j, ‖A i j‖ ≤ C) (y z : m → ℂ)
    (hy : v * sqLength y ≤ pairingRe A y y) (hz : sqLength z ≤ L * D) :
    v / 4 * sqLength (y+z) ≤ pairingRe A (y+z) (y+z) +
      (mixPrice v (countCeil m ^ 2 * C) * L) * D := by
  let M := countCeil m ^ 2 * C
  let Y := Real.sqrt (sqLength y)
  let Z := Real.sqrt (sqLength z)
  have hY : Y^2 = sqLength y := Real.sq_sqrt (sqLength_nonneg y)
  have hZ : Z^2 = sqLength z := Real.sq_sqrt (sqLength_nonneg z)
  have h₁ : -(M*Y*Z) ≤ pairingRe A y z :=
    (abs_le.mp (pairingRe_bound A hC he y z)).1
  have h₂ : -(M*Z*Y) ≤ pairingRe A z y :=
    (abs_le.mp (pairingRe_bound A hC he z y)).1
  have h₃ : -(M * sqLength z) ≤ pairingRe A z z :=
    (abs_le.mp (pairingRe_diag A hC he z)).1
  have hm : 2*M*Y*Z ≤ v/2 * sqLength y + 2*M^2/v * sqLength z := by
    rw [← hY, ← hZ]
    apply sub_nonneg.mp
    rw [show v/2 * Y^2 + 2*M^2/v * Z^2 - 2*M*Y*Z =
        (v*Y - 2*M*Z)^2 / (2*v) by field_simp; ring]
    positivity
  have hpay : 0 ≤ mixPrice v M := by unfold mixPrice M; positivity
  have hzz : mixPrice v M * sqLength z ≤ (mixPrice v M * L)*D := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hz hpay
  change v/4 * sqLength (y+z) ≤ pairingRe A (y+z) (y+z) + (mixPrice v M * L)*D
  apply le_trans _ (add_le_add_right hzz _)
  rw [pairingRe_expand]
  have hs := mul_le_mul_of_nonneg_left (sqLength_add y z) (by positivity : 0 ≤ v/4)
  unfold mixPrice
  linarith only [hs, hm, h₁, h₂, h₃, hy]

end YM.Work.F06
