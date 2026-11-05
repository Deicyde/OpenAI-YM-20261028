import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flux
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Polynomial
import YM.Progress.STATIONARY_SCENES.Frames
import YM.Push.PRICE_COMPILER.Post
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay

/-!
# Price the change of polynomial arguments (inside guards)

No cardinal cost here per coordinate choice needed in a polynomial in the
stated norm, still degree fixed; same repeated appearances counted. Use the
exact formula in GCC, with these polynomial consumers for unmarked or marked
local probes. Also a few simple L1 uses of the uniform tails; never involving
summing over different occurrences of a marker or of fields at different V.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function MeasureTheory Finset Matrix
open Next.SectorChange.Gaussian
open scoped Topology BigOperators Classical

variable {E I : Type} [NormedAddCommGroup E]
section obs
variable [Fintype I] {d D : ℕ} {c B L : ℝ}

/-- Lipschitz on polyradius with tested fee. Includes literal coefficient
norm of polynomials (proved below). `c` in both costs. -/
structure Sensitive (P : Vec I → E) (D : ℕ) (c : ℝ) : Prop extends TestPrice P D c where
  stable (x y : Vec I) (B : ℝ) (h : 1 ≤ B) (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) :
    ‖P x-P y‖ ≤ c*(D*B^D)*‖x-y‖

private lemma word_delta {A : Type} (i : Finset A) (h : 1 ≤ B) (x y : Vec I) (v : A → I)
    (hp : ‖x‖ ≤ B) (hq : ‖y‖ ≤ B) :
    ‖(∏ k∈i,(x (v k):ℂ))-(∏ k∈i,(y (v k):ℂ))‖ ≤ ↑i.card * B^i.card * ‖x-y‖ := by
  have hB := zero_le_one.trans h
  induction i using Finset.induction_on with
  | empty => simp
  | @insert a s ha hi =>
    have hl : ‖(x (v a):ℂ)-(y (v a):ℂ)‖ ≤ ‖x-y‖ := by
      rw [← Complex.ofReal_sub,Complex.norm_real]; exact norm_le_pi_norm (x-y) (v a)
    have he (z : Vec I) (hz : ‖z‖ ≤ B) k : ‖(z k : ℂ)‖ ≤ B := by
      rw [Complex.norm_real]; exact (norm_le_pi_norm z k).trans hz
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha, Nat.cast_add,Nat.cast_one]
    let X := (x (v a):ℂ); let Y:=(y (v a):ℂ); let p:=∏ k∈s,(x (v k):ℂ);let q:=∏ k∈s,(y (v k):ℂ)
    have ht : ‖q‖ ≤ B^s.card := by
      calc
        _ ≤ ∏ k∈s, ‖(y (v k):ℂ)‖ := norm_prod_le ..
        _ ≤ ∏ _k∈s,B := prod_le_prod (fun _ _ => norm_nonneg _) fun _ _ => he y hq _
        _ = _ := prod_const _
    rw [show X*p-Y*q=X*(p-q)+(X-Y)*q by ring]
    refine (norm_add_le ..).trans ?_
    rw [norm_mul,norm_mul]; apply le_trans (add_le_add (mul_le_mul (he _ hp _) hi (norm_nonneg _) hB)
      (mul_le_mul hl ht (norm_nonneg _) (norm_nonneg _)))
    rw [pow_succ]; nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h
      (pow_nonneg hB s.card)) (norm_nonneg (x-y))]

open Primitives.GCC in
lemma stable_polynomial (P : MvPolynomial I ℂ) (h : P.totalDegree ≤ D) :
    Sensitive (observe P) D (coefficientNorm P) := by
  refine { polynomial_test P h with stable := ?_ }
  intro x y B hB hx hy
  rw [observe_def,LocalPolynomial.exact_formula,LocalPolynomial.exact_formula, ← sum_sub_distrib,
    coefficientNorm, sum_mul,sum_mul]
  apply (norm_sum_le ..).trans
  refine sum_le_sum fun s hs => ?_
  rw [← mul_sub,norm_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold Words.verse; simp only [Words.entry, one_mul, zero_add]
  have hw := word_delta (Finset.univ (α:=LocalPolynomial.Key s)) hB x y (fun p => p.fst) hx hy
  have hG : (@Finset.univ (LocalPolynomial.Key s) _).card ≤ D := by
    rw [LocalPolynomial.key_length]
    exact (MvPolynomial.le_totalDegree hs).trans h
  exact hw.trans (mul_le_mul_of_nonneg_right (mul_le_mul (Nat.cast_le.mpr hG) (pow_le_pow_right₀ hB hG)
    (by positivity) (Nat.cast_nonneg _)) (norm_nonneg _))


end obs

section integral
variable [NormedSpace ℝ E] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integrable_product {G : Ω → ℝ} {P : Ω → E} (hP : Integrable P μ)
    (h : Measurable G) (hg : ∀ z, G z ∈ Set.Icc 0 1) :
    Integrable (fun z => G z • P z) μ := by
  apply hP.norm.mono'
  · exact h.aestronglyMeasurable.smul hP.aestronglyMeasurable
  refine Eventually.of_forall fun z => ?_
  rw [norm_smul,Real.norm_of_nonneg (hg z).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (hg z).2

/-- Removing Γ: price only on a subset with proved small measure for
this law. -/
lemma drop_guard {G : Ω → ℝ} (h : Measurable G) (hg : ∀ z, G z ∈ Set.Icc 0 1)
    (s : Set Ω) (hs : MeasurableSet s) (hr : ∀ z ∉ s, G z=1) {F : Ω → E} (hI : Integrable F μ) :
    ‖(∫ z, G z • F z ∂μ) - ∫ z,F z ∂μ‖ ≤ ∫ z in s, ‖F z‖ ∂μ := by
  have ht := integrable_product hI h hg
  rw [← integral_sub ht hI]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_indicator hs]
  apply integral_mono (ht.sub hI).norm (hI.norm.indicator hs)
  intro z
  change ‖G z • F z-F z‖ ≤ _
  rw [show G z • F z-F z=(G z-1) • F z by rw [sub_smul,one_smul]]
  by_cases he : z∈s
  · rw [Set.indicator_of_mem he,norm_smul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [Real.norm_eq_abs,abs_le]
    obtain ⟨h₁,h₂⟩ := hg z; constructor <;> linarith
  rw [hr z he,sub_self,zero_smul,norm_zero,Set.indicator_of_notMem he]

lemma inside [IsProbabilityMeasure μ] {f g : Ω → E} (hf : Integrable f μ) (hg : Integrable g μ) {C : ℝ}
    (h : ∀ z, ‖f z-g z‖ ≤ C) : ‖(∫ z, f z ∂μ) - ∫ z, g z ∂μ‖ ≤ C := by
  rw [← integral_sub hf hg]
  apply (norm_integral_le_integral_norm _).trans
  exact (integral_mono (hf.sub hg).norm (integrable_const _) h).trans_eq (by simp)

-- Same small_set type bound, *pulled back* to the full space; pays
-- directly with weightD even if the original integrand is shifted-data
-- times some c<1.
omit [NormedSpace ℝ E] in
lemma small_payment [Fintype I] [IsFiniteMeasure μ] {R : Ω → Vec I} {ν : Measure (Vec I)}
    (hp : MeasurePreserving R μ ν) {q D : ℕ} {A : ℝ} (hT : MomentBound ν q A) (he : 2*D≤q)
    (F : Ω → E) (c : ℝ) (hc : 0 ≤ c) (h : Integrable F μ) (hh : ∀ z, ‖F z‖ ≤ c * weight D (R z))
    (s : Set Ω) (hs : MeasurableSet s) (L : ℝ) (hL : 0<L) :
    (∫ z in s, ‖F z‖ ∂μ) ≤ c*(μ.real s * L + A/L) := by
  have hu := SectorTools.PhysicalGaussianSwitch.pay_pull hp _ hT.auth.aestronglyMeasurable
  have ht := hu.1.mpr hT.auth
  let w z := weight D (R z); let m z := weight q (R z); let a z := c*(L + m z / L)
  have hI : Integrable (fun z => m z/L) μ := ht.div_const L
  have hP : Integrable a μ := ((integrable_const L).add hI).const_mul c
  have ha z : w z ≤ L + m z / L := by
    by_cases hm : w z≤L
    · exact hm.trans (le_add_of_nonneg_right (div_nonneg (weight_nonneg ..) hL.le))
    have hz : w z*L ≤ m z := calc
      _ ≤ w z * w z := mul_le_mul_of_nonneg_left (le_of_not_ge hm) (weight_nonneg ..)
      _ = weight (D+D) (R z) := (weight_add ..).symm
      _ ≤ _ := weight_mono _ (show D+D≤q by omega)
    exact ((le_div_iff₀ hL).mpr hz).trans (le_add_of_nonneg_left hL.le)
  apply (setIntegral_mono_on h.norm.integrableOn hP.integrableOn hs fun z _ =>
    (hh z).trans (mul_le_mul_of_nonneg_left (ha z) hc)).trans
  unfold a
  rw [integral_const_mul,integral_add (integrable_const _) hI.integrableOn,
    setIntegral_const,smul_eq_mul,integral_div]
  apply mul_le_mul_of_nonneg_left (add_le_add_right _ _) hc
  apply div_le_div_of_nonneg_right _ hL.le
  exact (setIntegral_le_integral ht (Eventually.of_forall fun z => weight_nonneg ..)).trans (hu.2.le.trans hT.bound)
end integral
end YM.PhysicalNext.PhysicalGuard7f546.Curved
