import YM.Distribution.Product
import YM.Work.C13.Decay

/-!
# Exponential shifts of the interior test (C13)

The estimate on the remainder works at arbitrary frequency (not just when
`‖L x‖` is small). With the reserve it gives the derivative in the
Schwartz topology. The parameter derivative is with respect to all complex
variables at once; frequency derivatives are still real.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.C13

open Function Filter Asymptotics Boundary
open scoped Topology ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform bound for the Taylor remainder of the shift, in all frequency
derivative orders. It costs `exp (a * ‖x‖)` and a polynomial. -/
lemma norm_iteratedFDeriv_exp_remainder_le (L : E →L[ℝ] ℂ) (a : ℝ)
    (hLa : ‖L‖ ≤ a) (hL : ‖L‖ ≤ 1) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => Complex.exp (L y) - 1 - L y) x‖ ≤
      ‖L‖^2 * (1 + ‖x‖)^2 * Real.exp (a * ‖x‖) := by
  let f := fun y => Complex.exp (L y)
  let g := fun y => Complex.exp (L y) - 1
  let r := fun y => Complex.exp (L y) - 1 - L y
  have h (y : E) : HasFDerivAt r (scaleCLM L (g y)) y := by
    rw [scaleCLM_apply]
    dsimp only [g]
    rw [show (Complex.exp (L y) - 1) • L = Complex.exp (L y) • L - L by
      simpa using (sub_smul (Complex.exp (L y)) (1:ℂ) L)]
    exact ((L.hasFDerivAt.cexp.sub_const 1).sub L.hasFDerivAt)
  have hx := L.le_opNorm x
  have he : Real.exp ‖L x‖ ≤ Real.exp (a*‖x‖) := by
    apply Real.exp_le_exp.mpr
    exact hx.trans (mul_le_mul_of_nonneg_right hLa (norm_nonneg x))
  have hs : ‖x‖ ≤ 1 + ‖x‖ := by linarith
  have hsq : 1 + ‖x‖ ≤ (1 + ‖x‖)^2 := by nlinarith [norm_nonneg x]
  change ‖iteratedFDeriv ℝ j r x‖ ≤ _
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    calc
      ‖r x‖ ≤ ‖L x‖ ^ 2 * Real.exp ‖L x‖ := by
        simpa [r, Finset.sum_range_succ, sub_sub] using
          Complex.norm_exp_sub_sum_le_norm_mul_exp (L x) 2
      _ ≤ (‖L‖ * ‖x‖)^2 * Real.exp (a*‖x‖) := by gcongr
      _ ≤ _ := by rw [mul_pow]; gcongr
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv,
        show fderiv ℝ r = (scaleCLM L) ∘ g from funext fun y => (h y).fderiv]
    have hf : ContDiff ℝ j f := L.contDiff.cexp
    have hg : ContDiff ℝ j g := hf.sub contDiff_const
    have hu : ‖iteratedFDeriv ℝ j ((scaleCLM L) ∘ g) x‖ ≤
        ‖L‖ * ‖iteratedFDeriv ℝ j g x‖ :=
      ((scaleCLM L).norm_iteratedFDeriv_comp_left hg.contDiffAt le_rfl).trans
        (mul_le_mul_of_nonneg_right (norm_scaleCLM_le L) (norm_nonneg _))
    refine hu.trans ?_
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      have hh : ‖g x‖ ≤ (‖L‖ * (1+‖x‖)^2) * Real.exp (a * ‖x‖) := calc
        ‖g x‖ ≤ ‖L x‖ * Real.exp ‖L x‖ := by
          simpa [g] using Complex.norm_exp_sub_sum_le_norm_mul_exp (L x) 1
        _ ≤ (‖L‖ * ‖x‖) * Real.exp (a * ‖x‖) := by gcongr
        _ ≤ _ := by gcongr; exact hs.trans hsq
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by ring)
    | succ j =>
      have hgj : iteratedFDeriv ℝ (j+1) g x = iteratedFDeriv ℝ (j+1) f x := by
        change iteratedFDeriv ℝ (j+1) (f - fun _ => (1:ℂ)) x = _
        rw [iteratedFDeriv_sub_apply hf.contDiffAt contDiffAt_const, iteratedFDeriv_succ_const]
        simp
      have hpow : ‖L‖^(j+1) ≤ ‖L‖ := by
        rw [pow_succ]
        exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)
      have hh : ‖iteratedFDeriv ℝ (j+1) g x‖ ≤
          ‖L‖ * (1 + ‖x‖)^2 * Real.exp (a*‖x‖) := by
        rw [hgj]; apply (norm_iteratedFDeriv_exp_linear_le L x (j+1)).trans
        apply mul_le_mul _ _ (Real.exp_pos _).le (by positivity)
        · refine hpow.trans (le_mul_of_one_le_right (norm_nonneg _) ?_)
          linarith [norm_nonneg x]
        · exact (Real.exp_le_exp.mpr (Complex.re_le_norm _)).trans he
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by ring)

/-- Seminorm cost of the difference from the proposed linearization.
`r` will itself already be a test (difference of tests); the exponential
reserve then controls its size, quadratically in the shift. -/
lemma exists_exp_seminorm_cost (f : Probe E) {k j : ℕ} {a : ℝ}
    (hf : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      (1 + ‖x‖)^(k+2) * Real.exp (a * ‖x‖) * ‖iteratedFDeriv ℝ i f x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : E →L[ℝ] ℂ, ‖L‖ ≤ a → ‖L‖ ≤ 1 → ∀ r : Probe E,
      (∀ x, r x = f x * (Complex.exp (L x) - 1 - L x)) → Probe.size k j r ≤ ‖L‖^2 * C := by
  classical
  choose D hD hcost using hf
  have hsum : 0 ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * D i := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hD i)
  refine ⟨_, hsum, fun L ha hL r hr => ?_⟩
  let g := fun x => Complex.exp (L x) - 1 - L x
  have hg : ContDiff ℝ ∞ g := (L.contDiff.cexp.sub contDiff_const).sub L.contDiff
  refine SchwartzMap.seminorm_le_bound ℂ _ _ _ (mul_nonneg (sq_nonneg _) hsum) fun x => ?_
  rw [show (r : E → ℂ) = fun x => f x * g x from funext hr]
  apply le_trans (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (f.smooth ⊤) hg
    x (n := j) (by exact_mod_cast le_top)) (by positivity))
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hb : ‖iteratedFDeriv ℝ (j-i) g x‖ ≤ ‖L‖^2 * (1 + ‖x‖)^2 * Real.exp (a * ‖x‖) :=
    norm_iteratedFDeriv_exp_remainder_le L a ha hL _ x
  have hx : ‖x‖^k ≤ (1 + ‖x‖)^k := by gcongr; linarith
  calc
    _ ≤ (1 + ‖x‖)^k * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        (‖L‖^2 * (1 + ‖x‖)^2 * Real.exp (a * ‖x‖))) :=
      mul_le_mul hx (mul_le_mul_of_nonneg_left hb (by positivity)) (by positivity) (by positivity)
    _ = ‖L‖^2 * ((j.choose i : ℝ) *
        ((1 + ‖x‖)^(k+2) * Real.exp (a * ‖x‖) * ‖iteratedFDeriv ℝ i f x‖)) := by
      rw [pow_add]; ring
    _ ≤ _ := by gcongr; exact hcost i x

/-- Linear frequency multipliers act on genuine Schwartz probes. -/
def applyFrequency (L : E →L[ℝ] ℂ) (f : Probe E) : Probe E :=
  SchwartzMap.smulLeftCLM ℂ L f

lemma applyFrequency_apply (L : E →L[ℝ] ℂ) (f : Probe E) (x : E) :
    applyFrequency L f x = L x * f x :=
  SchwartzMap.smulLeftCLM_apply_apply L.hasTemperateGrowth f x

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

/-- Candidate complex derivative into the Schwartz space. -/
def shiftDeriv (B : P →L[ℂ] (E →L[ℝ] ℂ)) (f : Probe E) : P →L[ℂ] Probe E :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => applyFrequency (B v) f
    map_add' := fun v w => by
      ext1 x
      simp [applyFrequency_apply, add_mul]
    map_smul' := fun c v => by
      ext1 x
      simp [applyFrequency_apply, mul_assoc] }

lemma shiftDeriv_apply (B : P →L[ℂ] (E →L[ℝ] ℂ)) (f : Probe E) (v : P) (x : E) :
    shiftDeriv B f v x = B v x * f x := applyFrequency_apply _ f x

/-- Joint complex differentiation into the actual Schwartz topology. `T` is
only specified by the shift formula near `p`; elsewhere it may even be
discontinuous. -/
theorem hasFDerivAt_shift (B : P →L[ℂ] (E →L[ℝ] ℂ)) (T : P → Probe E) (p : P)
    (hp : ExpReserve (T p : E → ℂ))
    (hshift : ∀ᶠ q in 𝓝 p, ∀ x, T q x = Complex.exp (B (q-p) x) * T p x) :
    HasFDerivAt T (shiftDeriv B (T p)) p := by
  let R := fun q => T q - T p - shiftDeriv B (T p) (q-p)
  let N := fun q => (↑‖q-p‖ : ℂ)
  have hN : ∀ᶠ q in 𝓝 p, N q = 0 → R q = 0 := by
    refine Eventually.of_forall fun q hq => ?_
    have he : q = p := by simpa [N, sub_eq_zero] using hq
    subst q; simp [R]
  -- All weighted seminorms of the scaled difference tend to zero.
  have ht : Tendsto (fun q => (N q)⁻¹ • R q) (𝓝 p) (𝓝 0) := by
    apply (Probe.tendN _ _ _).mpr
    obtain ⟨a, ha, hf⟩ := hp.bound
    intro k j ε hε
    obtain ⟨C, hC, hcost⟩ := exists_exp_seminorm_cost (j := j) (T p) (hf (k+2))
    have hsmall : Tendsto (fun q => ‖B (q-p)‖) (𝓝 p) (𝓝 0) := Continuous.tendsto'
      (continuous_norm.comp (B.continuous.comp (continuous_id.sub continuous_const))) _ _ (by simp)
    have hlim : Tendsto (fun q => ‖B‖^2 * C * ‖q-p‖) (𝓝 p) (𝓝 0) := Continuous.tendsto'
      (continuous_const.mul (continuous_norm.comp (continuous_id.sub continuous_const))) _ _ (by simp)
    filter_upwards [hsmall.eventually_lt_const ha, hsmall.eventually_lt_const zero_lt_one, hshift,
      hlim.eventually_lt_const hε] with q hqa hq hT hlt
    have hR : Probe.size k j (R q) ≤ ‖B (q-p)‖^2 * C := by
      apply hcost _ hqa.le hq.le
      intro x
      simp [R, shiftDeriv_apply, hT x]
      ring
    rw [sub_zero, Probe.size]
    calc
      _ = ‖q-p‖⁻¹ * Probe.size k j (R q) := by simp [N, Probe.size, map_smul_eq_mul]
      _ ≤ ‖q-p‖⁻¹ * ((‖B‖ * ‖q-p‖)^2 * C) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply hR.trans
        apply mul_le_mul_of_nonneg_right _ hC
        exact pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) _
      _ = ‖B‖^2 * C * ‖q-p‖ := by
        by_cases hs : ‖q-p‖ = 0
        · simp [hs]
        · field_simp
      _ < ε := hlt
  rw [hasFDerivAt_iff_isLittleOTVS]
  have hr : R =o[ℂ; 𝓝 p] N := (isLittleOTVS_iff_tendsto_inv_smul hN).mpr ht
  refine hr.trans_isBigOTVS (IsBigO.isBigOTVS ?_)
  exact isBigO_of_le _ fun q => by simp [N]

end YM.Work.C13
