import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Tails
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.LocalPolynomial


/-!
# Probe compilation

No quotient on homogeneous polynomials or prescription of centered Wick
polynomials. Use the literal sum of complex coefficient norms. Thus mixed
and color terms and all their multiplicities are covered, independent of
any choice of estimates of a particular factor family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546
open MeasureTheory Function Filter Finset
open YM.Next.SectorChange.Gaussian YM.Primitives.GCC
open scoped Topology BigOperators

variable {I W : Type}

def coefficientNorm (P : MvPolynomial I ℂ) : ℝ := ∑ s∈P.support, ‖MvPolynomial.coeff s P‖
lemma coefficientNorm_nonneg (P : MvPolynomial I ℂ) : 0 ≤ coefficientNorm P :=
  sum_nonneg fun _ _ => norm_nonneg _

def observe (P : MvPolynomial I ℂ) (z : Vec I) : ℂ := MvPolynomial.aeval (fun i => (z i : ℂ)) P

lemma observe_def (P : MvPolynomial I ℂ) : observe P = LocalPolynomial.placed (fun _ => 0) 1 P := by
  funext z
  have he : Words.entry (fun _ : I => 0) 1 z=fun i => (z i : ℂ) := funext fun i => by
    simp [Words.entry]
  rw [LocalPolynomial.placed, he]; rfl

variable [Fintype I]

lemma observe_continuous (P : MvPolynomial I ℂ) : Continuous (observe P) := by
  rw [observe_def P, funext (LocalPolynomial.exact_formula _ _ _)]
  unfold Words.verse Words.entry
  fun_prop

/-- Literal `aeval` with the total-degree and coefficient budget. `Key`
uses **the exponent at every variable**, not the cardinality of nonzero
entries of the exponent. -/
lemma polynomial_size (P : MvPolynomial I ℂ) {D : ℕ} (h : P.totalDegree ≤ D) (z : Vec I) :
    ‖observe P z‖ ≤ coefficientNorm P * weight D z := by
  rw [observe_def, LocalPolynomial.exact_formula, coefficientNorm, sum_mul]
  refine (norm_sum_le ..).trans (sum_le_sum (fun s hs => ?_))
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hd : LocalPolynomial.length s ≤ D := (MvPolynomial.le_totalDegree hs).trans h
  unfold Words.verse
  apply (Finset.norm_prod_le ..).trans
  calc
    _ ≤ ∏ _i : LocalPolynomial.Key s, (1 + ‖z‖) := by
      apply prod_le_prod (fun _ _ => norm_nonneg _)
      intro i hi
      simp only [Words.entry, one_mul, zero_add, Complex.norm_real]
      exact (norm_le_pi_norm z i.fst).trans (le_add_of_nonneg_left zero_le_one)
    _ = weight (LocalPolynomial.length s) z := by rw [prod_const, LocalPolynomial.key_length]; rfl
    _ ≤ _ := weight_mono z hd

lemma polynomial_test (P : MvPolynomial I ℂ) {D : ℕ} (h : P.totalDegree ≤ D) :
    TestPrice (observe P) D (coefficientNorm P) :=
  ⟨coefficientNorm_nonneg _, (observe_continuous _).stronglyMeasurable, polynomial_size P h⟩

section mixes

-- distinct markers j indicate occurrences; the P_j/z coordinates need
-- not be distinct. Can take subfinsets too, using the same read set and
-- measure. Bills only polynomial evaluations, no support/control factors.
def mixedProbe (T : Finset W) (P : W → MvPolynomial I ℂ) (p : W → ℕ) (z : Vec I) :=
  ∏ j∈T, ‖observe (P j) z‖ ^ p j

def mixPrice (T : Finset W) (P : W → MvPolynomial I ℂ) (p : W → ℕ) : ℝ :=
  ∏ j∈T, coefficientNorm (P j) ^ p j

variable (T : Finset W) (P : W → MvPolynomial I ℂ) (p : W → ℕ)

omit [Fintype I] in
lemma mixed_nn (z : Vec I) : 0 ≤ mixedProbe T P p z :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _

omit [Fintype I] in
lemma mixed_price_nn : 0 ≤ mixPrice T P p := prod_nonneg fun _ _ =>
  pow_nonneg (coefficientNorm_nonneg _) _




end mixes
end YM.PhysicalNext.PhysicalGuard7f546
