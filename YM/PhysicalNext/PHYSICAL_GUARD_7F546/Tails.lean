import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Moment

/-!
# Tail prices

With varying read types, measures, fields and polynomials, use uniform
integrability in the *uniform large-value tail expectation* sense. Also get
the small-set estimate. Uniform in the class once the coefficient budget `c`
and the full moment price are bounded. No need to reindex measures into a
single measure space in order to state/pay these estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546
open MeasureTheory Set Filter
open YM.Next.SectorChange.Gaussian
open scoped Topology BigOperators

variable {E : Type*}
-- Vec uses `Type`; local read convention
section
variable {I : Type} [Fintype I] [NormedAddCommGroup E]

/-- A polynomial-class price on a test. -/
structure TestPrice (F : Vec I → E) (D : ℕ) (c : ℝ) : Prop where
  nonneg : 0 ≤ c
  measurable : StronglyMeasurable F
  size (z) : ‖F z‖ ≤ c * weight D z

lemma TestPrice.mono {F : Vec I → E} {D D' : ℕ} {c c' : ℝ}
    (h : TestPrice F D c) (hd : D ≤ D') (hc : c ≤ c') : TestPrice F D' c' :=
  ⟨h.nonneg.trans hc, h.measurable, fun z =>
    (h.size z).trans (mul_le_mul hc (weight_mono z hd) (weight_nonneg D z) (h.nonneg.trans hc))⟩

variable {μ : Measure (Vec I)} {q : ℕ} {A : ℝ} {F : Vec I → E} {D : ℕ} {c : ℝ}



lemma MomentBound.expect (h : MomentBound μ q A) (ht : TestPrice F D c) (hd : D ≤ q) :
    Integrable F μ ∧ (∫ z, ‖F z‖ ∂μ) ≤ c * A := by
  have hs := ht.mono hd le_rfl
  have hI := h.auth.const_mul c
  have hf := hI.mono' ht.measurable.aestronglyMeasurable (Eventually.of_forall hs.size)
  refine ⟨hf, (integral_mono hf.norm hI hs.size).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h.bound ht.nonneg

/-- Moment and tail estimates for the test under μ with q moment order. -/
structure TailPrice (μ : Measure (Vec I)) (F : Vec I → E) (q D : ℕ) (A c : ℝ) : Prop where
  test : TestPrice F D c
  auth : Integrable F μ
  l_one : (∫ z, ‖F z‖ ∂μ) ≤ c * A
  square : Integrable (fun z => ‖F z‖ ^ 2) μ
  second_moment : (∫ z, ‖F z‖ ^ 2 ∂μ) ≤ c ^ 2 * A
  radial (R : ℝ) (hR : 0 ≤ R) :
    (∫ z in {z : Vec I | R ≤ ‖z‖}, ‖F z‖ ∂μ) ≤ c / (1 + R)^(q - D) * A
  large (L : ℝ) (hL : 0 < L) :
    (∫ z in {z : Vec I | L ≤ ‖F z‖}, ‖F z‖ ∂μ) ≤ (c^2 * A) / L

theorem MomentBound.price (h : MomentBound μ q A) (ht : TestPrice F D c) (hd : 2 * D ≤ q) :
    TailPrice μ F q D A c := by
  obtain ⟨hf,h_one⟩ := h.expect ht (by omega)
  have ht' : TestPrice (fun z => ‖F z‖ ^ 2) (D + D) (c^2) := by
    refine ⟨sq_nonneg _, ht.measurable.norm.pow 2, fun z => ?_⟩
    change ‖(‖F z‖ ^ 2)‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _), weight_add, ← sq]
    calc
      _ ≤ (c * weight D z)^2 := pow_le_pow_left₀ (norm_nonneg _) (ht.size z) _
      _ = _ := mul_pow ..
  obtain ⟨hI,h_second⟩ := h.expect ht' (by omega)
  simp_rw [Real.norm_of_nonneg (sq_nonneg _)] at h_second
  refine ⟨ht, hf, h_one, hI, h_second, ?_, ?_⟩
  · intro R hR
    let s := {z : Vec I | R ≤ ‖z‖}
    have hs : MeasurableSet s := measurableSet_le measurable_const continuous_norm.measurable
    let r := (1 + R)^(q - D)
    have hr : 0 < r := by unfold r; positivity
    have hc : 0 ≤ c / r := div_nonneg ht.nonneg hr.le
    let g (z : Vec I) := (c / r) * weight q z
    have hg : Integrable g μ := h.auth.const_mul (c / r)
    have hy : ∀ z ∈ s, ‖F z‖ ≤ g z := by
      intro z hz
      have hq : r ≤ weight (q - D) z :=
        pow_le_pow_left₀ (show 0 ≤ 1 + R by linarith) (by linarith only [show R ≤ ‖z‖ from hz]) _
      apply (ht.size z).trans
      calc
        _ = (c / r * weight D z) * r := by field_simp
        _ ≤ (c / r * weight D z) * weight (q - D) z :=
          mul_le_mul_of_nonneg_left hq (mul_nonneg hc (weight_nonneg _ _))
        _ = _ := by rw [mul_assoc, ← weight_add, show D + (q - D) = q by omega]
    change (∫ z in s, ‖F z‖ ∂μ) ≤ c / r * A
    calc
      _ ≤ ∫ z in s, g z ∂μ := setIntegral_mono_on hf.norm.integrableOn hg.integrableOn hs hy
      _ ≤ ∫ z, g z ∂μ := setIntegral_le_integral hg
        (Eventually.of_forall fun z => mul_nonneg hc (weight_nonneg _ _))
      _ ≤ _ := by unfold g; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left h.bound hc
  · intro L hL
    let s := {z : Vec I | L ≤ ‖F z‖}
    have hs : MeasurableSet s := measurableSet_le measurable_const ht.measurable.norm.measurable
    let g (z : Vec I) := ‖F z‖ ^ 2 / L
    have hg : Integrable g μ := hI.div_const L
    have hy z (hz : z ∈ s) : ‖F z‖ ≤ g z := by
      unfold g
      rw [le_div_iff₀ hL, sq]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    calc
      _ ≤ ∫ z in s, g z ∂μ := setIntegral_mono_on hf.norm.integrableOn hg.integrableOn hs hy
      _ ≤ ∫ z, g z ∂μ := setIntegral_le_integral hg
        (Eventually.of_forall fun z => div_nonneg (sq_nonneg _) hL.le)
      _ ≤ _ := by unfold g; rw [integral_div]; exact div_le_div_of_nonneg_right h_second hL.le






end
end YM.PhysicalNext.PhysicalGuard7f546
