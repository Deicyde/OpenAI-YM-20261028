import YM.Distribution.Tests
import YM.Mink.Geometry

/-!
# Exponential reserves in all Schwartz seminorms (C13)

For a smooth temperate cutoff, to build one Schwartz test
`exp(L x) * cut x` we only need a strict exponential bound on the support.
Keep a reserve in the estimate, to absorb small shifts of `L` in the proof
of complex differentiability.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.C13

open Function Set Boundary
open scoped ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Auxiliary *real* continuous linear map for frequency derivatives. -/
def scaleCLM (L : E →L[ℝ] ℂ) : ℂ →L[ℝ] (E →L[ℝ] ℂ) :=
  (ContinuousLinearMap.lsmul ℝ ℂ :
    ℂ →L[ℝ] (E →L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] ℂ)).flip L

lemma scaleCLM_apply (L : E →L[ℝ] ℂ) (z : ℂ) : scaleCLM L z = z • L := rfl

lemma norm_scaleCLM_le (L : E →L[ℝ] ℂ) : ‖scaleCLM L‖ ≤ ‖L‖ :=
  (scaleCLM L).opNorm_le_bound (norm_nonneg _) fun z => by
    rw [scaleCLM_apply, norm_smul, mul_comm]

/-- The exponential of a real linear functional with complex values:
all frequency derivatives keep the exponential of the *real part*. -/
lemma norm_iteratedFDeriv_exp_linear_le (L : E →L[ℝ] ℂ) (x : E) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => Complex.exp (L y)) x‖ ≤ ‖L‖^j * Real.exp (L x).re := by
  let f := fun y => Complex.exp (L y)
  change ‖iteratedFDeriv ℝ j f x‖ ≤ _
  have h (y : E) : HasFDerivAt f (scaleCLM L (f y)) y := L.hasFDerivAt.cexp
  induction j with
  | zero => simp only [norm_iteratedFDeriv_zero, f, Complex.norm_exp, pow_zero, one_mul, le_refl]
  | succ j ih =>
    rw [← norm_iteratedFDeriv_fderiv,
        show fderiv ℝ f = (scaleCLM L) ∘ f from funext fun y => (h y).fderiv]
    have hf : ContDiff ℝ j f := L.contDiff.cexp
    apply ((scaleCLM L).norm_iteratedFDeriv_comp_left hf.contDiffAt le_rfl).trans
    calc
      _ ≤ ‖L‖ * (‖L‖^j * Real.exp (L x).re) :=
        mul_le_mul (norm_scaleCLM_le L) ih (norm_nonneg _) (norm_nonneg _)
      _ = _ := by rw [pow_succ]; ring

/-- Pay for polynomial factors with part of the strict exponential. -/
lemma exists_polynomial_exp_bound (A : ℝ) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → (1+t)^k * Real.exp (A-a*t) ≤ C := by
  refine ⟨k.factorial / a^k * Real.exp (A+a), by positivity, fun t ht => ?_⟩
  have hp := Real.pow_div_factorial_le_exp (x := a*(1+t)) (by positivity) k
  calc
    (1+t)^k * Real.exp (A-a*t) =
        k.factorial / a^k * ((a*(1+t))^k / k.factorial) * Real.exp (A-a*t) := by
          rw [mul_pow]
          field_simp
    _ ≤ k.factorial / a^k * Real.exp (a*(1+t)) * Real.exp (A-a*t) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- A Schwartz estimate with an exponential reserve, at one function
(no uniformity in words). Includes smoothness. -/
structure ExpReserve (f : E → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ f
  bound : ∃ a : ℝ, 0 < a ∧ ∀ k j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
    (1 + ‖x‖)^k * Real.exp (a * ‖x‖) * ‖iteratedFDeriv ℝ j f x‖ ≤ C

namespace ExpReserve

/-- Make the actual test. -/
def toProbe {f : E → ℂ} (h : ExpReserve f) : Probe E where
  toFun := f
  smooth' := h.smooth
  decay' k j := by
    obtain ⟨a, ha, H⟩ := h.bound
    obtain ⟨C, -, hC⟩ := H k j
    refine ⟨C, fun x => ?_⟩
    refine le_trans ?_ (hC x)
    have he : 1 ≤ Real.exp (a * ‖x‖) := Real.one_le_exp (by positivity)
    have hk : ‖x‖^k ≤ (1+‖x‖)^k := by gcongr; linarith
    exact mul_le_mul_of_nonneg_right (hk.trans (le_mul_of_one_le_right (by positivity) he))
      (norm_nonneg _)

lemma toProbe_apply {f : E → ℂ} (h : ExpReserve f) (x : E) : h.toProbe x = f x := rfl

/-- Exponential reserve for an interior imaginary part. Only the bound on
`tsupport cut` matters. -/
theorem of_cut {cut : E → ℂ} (hcut : cut.HasTemperateGrowth)
    (L : E →L[ℝ] ℂ) {A c : ℝ} (hc : 0 < c)
    (hL : ∀ x ∈ tsupport cut, (L x).re ≤ A - c*‖x‖) :
    ExpReserve (fun x => Complex.exp (L x) * cut x) := by
  let f : E → ℂ := fun x => Complex.exp (L x)
  have hf : ContDiff ℝ ∞ f := L.contDiff.cexp
  change ExpReserve (fun x => f x * cut x)
  refine ⟨hf.mul hcut.1, c/2, half_pos hc, fun k j => ?_⟩
  obtain ⟨m, C, hC, hbound⟩ := hcut.norm_iteratedFDeriv_le_uniform j
  obtain ⟨B, hB, hpoly⟩ := exists_polynomial_exp_bound A (half_pos hc) (k+m)
  refine ⟨∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * ‖L‖^i * C * B, by positivity, fun x => ?_⟩
  by_cases hx : x ∈ tsupport cut
  · apply le_trans (mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_mul_le hf hcut.1 x (n := j) (by exact_mod_cast le_top)) (by positivity))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have he : ‖iteratedFDeriv ℝ i f x‖ ≤ ‖L‖^i * Real.exp (A-c*‖x‖) :=
      (norm_iteratedFDeriv_exp_linear_le L x i).trans (by gcongr; exact hL x hx)
    have hh := hbound (j-i) (Nat.sub_le j i) x
    have heq : Real.exp (c/2 * ‖x‖) * Real.exp (A-c*‖x‖) = Real.exp (A - c/2 * ‖x‖) := by
      rw [← Real.exp_add]; ring_nf
    calc
      _ ≤ (1 + ‖x‖)^k * Real.exp (c/2 * ‖x‖) *
          ((j.choose i : ℝ) * (‖L‖^i * Real.exp (A-c*‖x‖)) * (C * (1 + ‖x‖)^m)) := by gcongr
      _ = (j.choose i : ℝ) * ‖L‖^i * C * ((1 + ‖x‖)^(k+m) * Real.exp (A - c/2 * ‖x‖)) := by
        rw [← heq, pow_add]; ring
      _ ≤ _ := by gcongr; exact hpoly _ (norm_nonneg _)
  have hs : tsupport (iteratedFDeriv ℝ j (fun x => f x * cut x)) ⊆ tsupport cut :=
    (tsupport_iteratedFDeriv_subset j).trans tsupport_mul_subset_right
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), norm_zero, mul_zero]
  positivity

end ExpReserve

end YM.Work.C13
