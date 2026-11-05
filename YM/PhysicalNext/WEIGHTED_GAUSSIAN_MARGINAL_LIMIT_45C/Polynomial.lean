import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Comparison
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Laws
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.LocalPolynomial


/-!
# All complex polynomials, on the two committed marginals

Eval with inclusion of the actual real counting variables into ℂ. Even
for the raw reads, use `GCC.LocalPolynomial.produce` on that price;
keeps their factorial/multiplicity bookkeeping (`Key s=Σ i, Fin (s i)`
on a monomial) intact, genuine covariance beneath. No Wick formulas for
this extension. Raw polynomial income pays also for its mean and coupling,
not uniformly bounded in β. `absMixed` useful even for repeated powers of
one link/color in a common patch, writing the mixed-moment/tail control
for all such monomials simultaneously once the user buys K and degree d.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange (Gaussian.Table)
open Next.SectorChange.Gaussian
open AnalyticBridge.LocalGaussianLaws
open Primitives.GCC
open SectorTools
open SectorTools.PhysicalGaussianSwitch (shift)
open scoped Topology BigOperators

variable {I : Type} {K d : ℕ} {E M x : ℝ}

/-- Coefficient norm convention here and in the estimates. -/
def coefficientNorm (P : MvPolynomial I ℂ) : ℝ := ∑ s∈P.support, ‖MvPolynomial.coeff s P‖
lemma coefficientNorm_nonneg (P : MvPolynomial I ℂ) : 0 ≤ coefficientNorm P := by
  unfold coefficientNorm; positivity

/-- Eval an actual polynomial on the real reads (no shift parameter hidden
in the evaluation). -/
def peval (P : MvPolynomial I ℂ) (z : Vec I) : ℂ := MvPolynomial.aeval (fun i => (z i : ℂ)) P
lemma peval_raw (P : MvPolynomial I ℂ) (b : Vec I) (g : ℝ) :
    peval P ∘ restoreRead b g = LocalPolynomial.placed (fun i => (b i:ℂ)) (g:ℂ) P := by
  funext z; unfold peval restoreRead LocalPolynomial.placed Words.entry Function.comp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]

/-- Extra coefficient-wise multiplier paid for evaluation at `b+g*z`.
Takes the sup coordinate norm bound B for b, real g. -/
def polyBill (K : ℕ) (E : ℝ) (d : ℕ) (B g : ℝ) :=
  (d.factorial:ℝ)*(max 1 (B + |g| * Real.sqrt (((d:ℝ)+1)/(reserve K E))))^d
lemma polyBill_nonneg (K : ℕ) (E : ℝ) (d : ℕ) (B g : ℝ) : 0 ≤ polyBill K E d B g := by
  unfold polyBill; positivity

variable [Fintype I] [DecidableEq I]

/-- Use the existing producer and bound in terms of the specified
coefficient norm. b, g in raw units. -/
lemma on_polynomial (P : MvPolynomial I ℂ) (hP : P.totalDegree ≤ d) (b : Vec I) (g : ℝ) (hE : 0 ≤ E) :
    Moderate K E (coefficientNorm P * polyBill K E d ‖b‖ g) (peval P ∘ restoreRead b g) := by
  rw [peval_raw]
  let r := reserve K E
  let w : Vec I := fun _ => r
  let m := fun i => (b i:ℂ)
  have hr : 0 < r := reserve_pos K hE
  obtain ⟨-,h⟩ := LocalPolynomial.produce m (g:ℂ) P 0 d hP Finset.univ (fun _ _ => Finset.subset_univ _)
    w (fun _ => hr.le) r ‖b‖ hr (norm_nonneg _) (fun i _ => ⟨le_rfl,(Complex.norm_real _).le.trans (norm_le_pi_norm b i)⟩)
  have hx := LocalPolynomial.pile (g:ℂ) P 0 d hP r ‖b‖ (norm_nonneg _)
  have hy : LocalPolynomial.cap (g:ℂ) P r d ‖b‖ 0 ≤ coefficientNorm P * polyBill K E d ‖b‖ g := by
    simpa only [pow_zero, mul_one, LocalPolynomial.lump, coefficientNorm, Words.bulk,
      Words.height, Complex.norm_real, Real.norm_eq_abs, polyBill, mul_assoc] using hx
  refine ⟨mul_nonneg (coefficientNorm_nonneg P) (polyBill_nonneg ..), (h.charm [] (by simp)).measurable, fun z => ?_⟩
  refine (h.price [] (by simp) z).trans ?_
  rw [show Multi.Vacuum.Gauss.pay w z = _ from pay_const z r]
  exact mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le

/-- This particular bill is independent of the polynomial (its degree
was fixed and its coefficient norm is counted separately) and of x. -/
def normalBill (K : ℕ) (E : ℝ) (d : ℕ) := polyBill K E d 0 1

def normalError (K : ℕ) (E : ℝ) (d : ℕ) (x : ℝ) := normalBill K E d * errorUnit K E x


lemma poly_price (P : MvPolynomial I ℂ) (hP : P.totalDegree ≤ d) (hE : 0 ≤ E) :
    Moderate K E (coefficientNorm P * normalBill K E d) (peval P) := by
  simpa only [normalBill, norm_zero,show restoreRead (0:Vec I) 1 = id from funext fun z => by simp [restoreRead],comp_id]
    using on_polynomial (K:=K) P hP 0 1 hE

variable {C B : Gaussian.Table I} {δ : Vec I}





section uniform

omit [DecidableEq I] in
/-- One UI form on normalized locations, across P and laws and read
spaces. The family in the physical application has all these hypotheses
proved on the two actual measures. -/
theorem ui_polynomial (μ : Measure (Vec I)) [IsFiniteMeasure μ] (P : MvPolynomial I ℂ)
    (h : Costed K E (coefficientNorm P * normalBill K E d) μ (id : Vec I → Vec I) (peval P))
    (hP : coefficientNorm P ≤ 1) {ε : ℝ} (he : 0 < ε) :
    let t := valueLevel K E (normalBill K E d) ε
    ((∫ z, ‖peval P z‖ ∂μ) ≤ normalBill K E d*kiln K E) ∧
    (∀ u, t ≤ u → (∫ z in {z| u ≤ ‖peval P z‖}, ‖peval P z‖ ∂μ) ≤ ε/2) ∧
      0 < ε/(2*t) ∧ ∀ s : Set (Vec I), μ.real s ≤ ε/(2*t) → (∫ z in s, ‖peval P z‖ ∂μ) ≤ ε := by
  have hh : coefficientNorm P * normalBill K E d ≤ normalBill K E d :=
    mul_le_of_le_one_left (polyBill_nonneg ..) hP
  intro t
  exact ⟨h.first_bound.trans (mul_le_mul_of_nonneg_right hh (kiln_pos ..).le),h.uniform hh he⟩
end uniform

/-- Absolute mixed monomial, with repeated read exponents as given. -/
def absMixed (s : I →₀ ℕ) (z : Vec I) := ∏ i, |z i|^s i
omit [DecidableEq I] in
lemma absMixed_nonneg (s : I →₀ ℕ) (z : Vec I) : 0 ≤ absMixed s z := by unfold absMixed; positivity
omit [DecidableEq I] in
lemma absMixed_eq (s : I →₀ ℕ) (z : Vec I) : absMixed s z = ‖peval ((MvPolynomial.monomial s) 1) z‖ := by
  unfold peval absMixed
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp [Complex.norm_real, Real.norm_eq_abs]
omit [Fintype I] in
lemma coefficient_monomial (s : I →₀ ℕ) : coefficientNorm ((MvPolynomial.monomial s) 1) = 1 := by
  classical
  unfold coefficientNorm
  simp [MvPolynomial.support_monomial, MvPolynomial.coeff_monomial]








end YM.PhysicalNext.WeightedGaussianMarginal45C
