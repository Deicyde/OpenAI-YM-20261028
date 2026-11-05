import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic




/-!
# Common conditional Gaussian estimates for the mixed vertices

Here Q(x,x) has the 1/2 in it already. Estimate in the actual dimension of the
*joint marginal*. At fixed order polynomial in that dimension and in the inverse
precision bound; simply paying a C per coordinate of a held argument would
not buy the mixed step. Dilation works also with the product sup norm, for
spaces of real-color arrays. See other files for applications, inputs about
real covariances; these results don't provide those covariances.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels.Gaussian
open Function Filter Module MeasureTheory Measure
open scoped NNReal ENNReal Topology BigOperators Classical

/-- Polynomial-exponential trade used for holding *all* link coordinates
of the input marked operands. We want to be able to use d depending on the
word (e.g. reciprocal of dimension), so not `IsBigO` with unpriced constants. -/
lemma reserve {d r : ℝ} (k : ℕ) (hd : 0 < d) (hr : 0 ≤ r) :
    (1+r)^k ≤ (2+(k:ℝ)/d)^k * Real.exp (d*r^2) := by
  rcases eq_zero_or_pos k with h|h
  · subst k; simpa using! Real.one_le_exp (by positivity : 0 ≤ d*r^2)
  have hk : 0 < (k:ℝ) := Nat.cast_pos.mpr h
  by_cases ht : r ≤ 1
  · refine le_trans (pow_le_pow_left₀ (by positivity) (show 1+r ≤ 2+(k:ℝ)/d by linarith [div_pos hk hd]) k) ?_
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  let x := d*r^2/k
  have hx : 0 ≤ x := by unfold x; positivity
  have h1 := Real.one_le_exp hx
  have h2 : r ≤ ((k:ℝ)/d)*x := by
    rw [show ((k:ℝ)/d)*x=r^2 by unfold x; field_simp]
    nlinarith
  have H : 1+r ≤ (2+(k:ℝ)/d)*Real.exp x := by
    have hb : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    linarith only [h2, mul_le_mul_of_nonneg_left hb (div_nonneg hk.le hd.le), h1]
  apply le_trans (pow_le_pow_left₀ (by positivity) H k)
  rw [mul_pow, ← Real.exp_nat_mul, show (k:ℝ)*x=d*r^2 by unfold x; field_simp]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

abbrev Quad (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E →L[ℝ] ℝ
def raw (Q : Quad E) (x : E) := Real.exp (- Q x x)
def zMass (Q : Quad E) := ∫ x,raw Q x ∂μ
def pdf (Q : Quad E) (x : E) := raw Q x / zMass μ Q

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma raw_cont (Q : Quad E) : Continuous (raw Q) := by unfold raw; fun_prop

variable {Q : Quad E} {c : ℝ} (hc : 0<c) (h : ∀ x, c*‖x‖^2 ≤ Q x x)
include hc h

lemma polynomial_integrable (k : ℕ) : Integrable (fun x => raw Q x*(1+‖x‖)^k) μ := by
  let n := finrank ℝ E + 1
  have hn : (finrank ℝ E:ℝ)<(n:ℝ) := by unfold n; exact_mod_cast Nat.lt_succ_self _
  have hf := (integrable_one_add_norm (μ:=μ) hn)
  let K := (2+((k+n:ℕ):ℝ)/c)^(k+n)
  refine (hf.const_mul K).mono' ((by unfold raw; fun_prop : Continuous (fun x => raw Q x*(1+‖x‖)^k)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  unfold raw
  rw [Real.norm_of_nonneg (by positivity),mul_assoc,←pow_add]
  refine (mul_le_mul_of_nonneg_left (reserve (k+n) hc (norm_nonneg _)) (Real.exp_pos _).le).trans ?_
  rw [mul_left_comm,← Real.exp_add]
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by linarith [h x]))

lemma raw_integrable : Integrable (raw Q) μ := by simpa using! polynomial_integrable μ hc h 0
lemma zMass_pos : 0 < zMass μ Q := integral_pos_of_integrable_nonneg_nonzero (x:=0) (raw_cont Q)
    (raw_integrable μ hc h) (fun _ => (Real.exp_pos _).le) (Real.exp_pos _).ne'
lemma pdf_pos (x : E) : 0 < pdf μ Q x := div_pos (Real.exp_pos _) (zMass_pos μ hc h)
lemma weighted_integrable (k : ℕ) : Integrable (fun x => pdf μ Q x*(1+‖x‖)^k) μ := by
  unfold pdf; simp_rw [div_mul_eq_mul_div]; exact (polynomial_integrable μ hc h k).div_const _
lemma pdf_integrable : Integrable (pdf μ Q) μ := by simpa using! weighted_integrable μ hc h 0

lemma normalized : (∫ x,pdf μ Q x ∂μ)=1 := by
  unfold pdf; rw [integral_div]; exact div_self (zMass_pos μ hc h).ne'

def expense (n k : ℕ) (c : ℝ) := (2+(k:ℝ)/(c/(2*(1+(n:ℝ)))))^k * Real.exp 1

lemma weighted_bill (k : ℕ) :
    (∫ x,pdf μ Q x*(1+‖x‖)^k ∂μ) ≤ expense (finrank ℝ E) k c := by
  let f := pdf μ Q
  let n := finrank ℝ E
  let s : ℝ := 1+1/(1+(n:ℝ))
  have hp : 1+(n:ℝ) > 0 := by positivity
  have hs : 1 ≤ s := by unfold s; bound
  have hd : 0 < s := lt_of_lt_of_le zero_lt_one hs
  let d := c/(2*(1+(n:ℝ)))
  have ht : 0<d := by unfold d; positivity
  let U := (2+(k:ℝ)/d)^k
  have hu : 0 ≤ U := by unfold U; positivity
  have hn : s^n ≤ Real.exp 1 := by
    let r := 1/(1+(n:ℝ))
    have he : s ≤ Real.exp r := by simpa only [add_comm r 1] using Real.add_one_le_exp r
    apply le_trans (pow_le_pow_left₀ hd.le he n)
    rw [← Real.exp_nat_mul]; apply Real.exp_monotone
    unfold r; rw [← mul_div_assoc, mul_one, div_le_one hp]; linarith
  have hI : ∀ x : E, pdf μ Q x*(1+‖x‖)^k ≤ U*f (s⁻¹ • x) := by
    intro x
    have he : (1+‖x‖)^k ≤ U * Real.exp (d*‖x‖^2) := reserve k ht (norm_nonneg x)
    apply le_trans (mul_le_mul_of_nonneg_left he (pdf_pos μ hc h _).le)
    rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ hu
    unfold f pdf raw
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    refine div_le_div_of_nonneg_right (Real.exp_monotone ?_) (zMass_pos μ hc h).le
    have he : Q (s⁻¹ • x) (s⁻¹ • x) = s⁻¹^2 * Q x x := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul, pow_two, mul_assoc]
    rw [he]
    have hv : s⁻¹ ^2 ≤ s⁻¹ := by have := inv_pos.mpr hd; nlinarith [inv_le_one_of_one_le₀ hs]
    have hx : 0≤Q x x := (by positivity : 0 ≤ c*‖x‖^2).trans (h x)
    have hw : 1/(2*(1+(n:ℝ))) ≤ 1-s⁻¹ := by
      unfold s; field_simp; nlinarith [show (0:ℝ) ≤ n by positivity]
    have hy : d*‖x‖^2 ≤ (1-s⁻¹)*Q x x := by
      rw [show d=c*(1/(2*(1+(n:ℝ)))) by unfold d; ring,mul_comm c,mul_assoc]
      exact mul_le_mul hw (h x) (by positivity) (by linarith [show 0 ≤ 1/(2*(1+(n:ℝ))) by positivity])
    linarith only [hy,mul_le_mul_of_nonneg_right hv hx]
  calc
    _ ≤ ∫ x,U*f (s⁻¹ • x) ∂μ := integral_mono (weighted_integrable μ hc h k)
      (((pdf_integrable μ hc h).comp_smul (inv_pos.mpr hd).ne').const_mul U) hI
    _ = U*s^n := by rw [integral_const_mul, μ.integral_comp_inv_smul_of_nonneg f hd.le, show (∫ x,f x ∂μ)=1 from normalized μ hc h, smul_eq_mul,mul_one]
    _ ≤ U*Real.exp 1 := by gcongr

lemma raw_bill (k : ℕ) :
    (∫ x,raw Q x*(1+‖x‖)^k ∂μ) ≤ expense (finrank ℝ E) k c * zMass μ Q := by
  apply (div_le_iff₀ (zMass_pos μ hc h)).mp
  have hv := weighted_bill μ hc h k
  simp only [pdf,div_mul_eq_mul_div,integral_div] at hv; exact hv

end YM.Further.DenseMixedKernels.Gaussian
