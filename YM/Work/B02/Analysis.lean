import Mathlib.Analysis.Calculus.MeanValue
import YM.Hilbert.Kolmogorov


/-!
# Norm estimates for real derivatives via complex matrix elements

Use local calculus on plant matrix elements; inherit it on finite sums; use
bounds in *Hilbert* norm, not in the space of formal finite sums. Estimate a
remainder with the scalar mean value inequality. Obtain an operator-norm
bound on this remainder using density in the same Gram Hilbert space.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.B02
open Function Filter Set Metric
open scoped InnerProductSpace Topology NNReal BigOperators ComplexConjugate

section Observe

variable {H : Hilbert}

/-- Probe a matrix element, conjugate linear in `u`, linear in `v`.
The functional here on operators only needs to be bundled real-linear. -/
def observe (u v : H) : H.Op →L[ℝ] ℂ :=
  ((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ H.space v)).restrictScalars ℝ

theorem observe_apply (u v : H) (T : H.Op) : observe u v T = inner ℂ u (T v) := rfl

private theorem observe_add_left (u v w : H) :
    observe (u + v) w = observe u w + observe v w := by
  ext1 T
  simp [observe_apply, inner_add_left]

private theorem observe_add_right (u v w : H) :
    observe u (v + w) = observe u v + observe u w := by
  ext1 T
  simp [observe_apply, inner_add_right]

private theorem observe_smul_left (u v : H) (c : ℂ) :
    observe (c • u) v = conj c • observe u v := by
  ext1 T
  simp [observe_apply, inner_smul_left]

private theorem observe_smul_right (u v : H) (c : ℂ) :
    observe u (c • v) = c • observe u v := by
  ext1 T
  simp [observe_apply, inner_smul_right]

private theorem observe_zero_left (v : H) : observe 0 v = 0 := by
  ext1 T
  simp [observe_apply]

private theorem observe_zero_right (v : H) : observe v 0 = 0 := by
  ext1 T
  simp [observe_apply]

theorem observe_norm_le (u v : H) : ‖observe u v‖ ≤ ‖u‖ * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro Z
  rw [observe_apply]
  calc
    ‖inner ℂ u (Z v)‖ ≤ ‖u‖ * ‖Z v‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖Z‖ * ‖v‖) := mul_le_mul_of_nonneg_left (Z.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

end Observe

variable {X : Type} {K : X → X → ℂ} (J : Kernel.Gram K)

theorem norm_le_of_stem_bounds (Z : J.H.Op) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ f g : X →₀ ℂ,
      ‖observe (J.stems f) (J.stems g) Z‖ ≤ ‖J.stems f‖ * ‖J.stems g‖ * C) :
    ‖Z‖ ≤ C := by
  have ha (u v : J.H) : ‖inner ℂ u (Z v)‖ ≤ ‖u‖ * ‖v‖ * C := by
    refine J.whole.induction_on₂ (p := fun a b => ‖inner ℂ a (Z b)‖ ≤ ‖a‖ * ‖b‖ * C)
      ?_ hz u v
    exact isClosed_le (by fun_prop) (by fun_prop)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  by_cases he : Z v = 0
  · rw [he, norm_zero]
    positivity
  have hh := ha (Z v) v
  rw [inner_self_eq_norm_sq_to_K] at hh
  apply le_of_mul_le_mul_left _ (norm_pos_iff.mpr he)
  calc
    ‖Z v‖ * ‖Z v‖ ≤ ‖Z v‖ * ‖v‖ * C := by simpa [pow_two] using hh
    _ = _ := by ring

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → J.H.Op} {f' : E → E →L[ℝ] J.H.Op}

theorem stem_derivs {B : E →L[ℝ] J.H.Op} {x : E}
    (h : ∀ p q : X, HasFDerivAt (fun y => observe (J.plant p) (J.plant q) (f y))
      ((observe (J.plant p) (J.plant q)).comp B) x) :
    ∀ u v : X →₀ ℂ, HasFDerivAt (fun y => observe (J.stems u) (J.stems v) (f y))
      ((observe (J.stems u) (J.stems v)).comp B) x := by
  let Tests (L : J.H.Op →L[ℝ] ℂ) : Prop := HasFDerivAt (fun y => L (f y)) (L.comp B) x
  have hzero : Tests 0 := by
    unfold Tests
    rw [ContinuousLinearMap.zero_comp]
    exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x
  have hadd (L M : J.H.Op →L[ℝ] ℂ) (hL : Tests L) (hM : Tests M) : Tests (L + M) := by
    unfold Tests at *
    rw [ContinuousLinearMap.add_comp]
    exact hL.add hM
  have hscale (L : J.H.Op →L[ℝ] ℂ) (c : ℂ) (hL : Tests L) : Tests (c • L) := by
    unfold Tests at *
    rw [ContinuousLinearMap.smul_comp]
    exact hL.const_smul c
  have aux (p : X) (v : X →₀ ℂ) : Tests (observe (J.plant p) (J.stems v)) := by
    induction v using Finsupp.induction_linear with
    | zero => rw [map_zero, observe_zero_right]; exact hzero
    | add v w hv hw => rw [map_add, observe_add_right]; exact hadd _ _ hv hw
    | single b c =>
      rw [Kernel.Gram.stems, Finsupp.linearCombination_single, observe_smul_right]
      exact hscale _ _ (h p b)
  intro u v
  change Tests (observe (J.stems u) (J.stems v))
  induction u using Finsupp.induction_linear with
  | zero => rw [map_zero, observe_zero_left]; exact hzero
  | add a b ha hb => rw [map_add, observe_add_left]; exact hadd _ _ ha hb
  | single a c =>
    rw [Kernel.Gram.stems, Finsupp.linearCombination_single, observe_smul_left]
    exact hscale _ _ (aux a v)

/-- A scalar mean value estimate with constants uniform in the observing
vectors, thus giving operator-norm control. Does not assume the operators
vary norm continuously. -/
theorem norm_remainder {s : Set E} {x y : E} {C : ℝ} (hC : 0 ≤ C)
    {B : E →L[ℝ] J.H.Op}
    (hder : ∀ z ∈ s, ∀ p q : X, HasFDerivAt
      (fun y => observe (J.plant p) (J.plant q) (f y))
      ((observe (J.plant p) (J.plant q)).comp (f' z)) z)
    (hb : ∀ z ∈ s, ‖f' z - B‖ ≤ C) (hs : Convex ℝ s) (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - B (y - x)‖ ≤ C * ‖y - x‖ := by
  apply norm_le_of_stem_bounds J _ _ (by positivity)
  intro u v
  let L := observe (J.stems u) (J.stems v)
  have hL z (hz : z ∈ s) : HasFDerivWithinAt (fun y => L (f y)) (L.comp (f' z)) s z :=
    (stem_derivs J (hder z hz) u v).hasFDerivWithinAt
  have hbnd z (hz : z ∈ s) : ‖L.comp (f' z) - L.comp B‖ ≤ ‖J.stems u‖ * ‖J.stems v‖ * C := by
    calc
      _ = ‖L.comp (f' z - B)‖ := by rw [ContinuousLinearMap.comp_sub]
      _ ≤ ‖L‖ * ‖f' z - B‖ := ContinuousLinearMap.opNorm_comp_le ..
      _ ≤ _ := mul_le_mul (observe_norm_le ..) (hb z hz) (norm_nonneg (f' z - B)) (by positivity)
  have hi := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' hL hbnd hx hy
  change ‖L _‖ ≤ _
  simpa only [map_sub, ContinuousLinearMap.comp_apply, mul_assoc] using hi

/-- First use of the remainder estimate: get norm continuity from locally
bounded candidate for the derivative and correct plant matrix element derivatives. -/
theorem continuousAt_of_plant_derivs {x : E}
    (hder : ∀ᶠ z in 𝓝 x, ∀ p q : X, HasFDerivAt
      (fun y => observe (J.plant p) (J.plant q) (f y))
      ((observe (J.plant p) (J.plant q)).comp (f' z)) z)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᶠ z in 𝓝 x, ‖f' z‖ ≤ C) : ContinuousAt f x := by
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp (hder.and hb)
  have hl : LipschitzOnWith ⟨C,hC⟩ f (ball x ε) := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro y hy z hz
    have hb' (w) (hw : w ∈ ball x ε) : ‖f' w - 0‖ ≤ C := by
      rw [sub_zero]
      exact (he hw).2
    change ‖f y - f z‖ ≤ C * ‖y - z‖
    simpa using
      norm_remainder J hC (fun w hw => (he hw).1) hb' (convex_ball _ _) hz hy
  exact hl.continuousOn.continuousAt (ball_mem_nhds _ hε)

/-- Second use of the remainder estimate: get a true Fréchet derivative in
operator norm once the claimed derivative is norm continuous. -/
theorem hasFDerivAt_of_plant_derivs {x : E}
    (hder : ∀ᶠ z in 𝓝 x, ∀ p q : X, HasFDerivAt
      (fun y => observe (J.plant p) (J.plant q) (f y))
      ((observe (J.plant p) (J.plant q)).comp (f' z)) z)
    (hcont : ContinuousAt f' x) : HasFDerivAt f (f' x) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp (inter_mem hder (hcont <| ball_mem_nhds (f' x) hc))
  filter_upwards [ball_mem_nhds x hε] with y hy
  have hb z (hz : z ∈ ball x ε) : ‖f' z - f' x‖ ≤ c := by
    calc
      _ = dist (f' z) (f' x) := (dist_eq_norm (f' z) (f' x)).symm
      _ ≤ c := le_of_lt (show dist (f' z) (f' x) < c from (he hz).2)
  exact norm_remainder J hc.le (fun w hw => (he hw).1) hb (convex_ball _ _)
    (mem_ball_self hε) hy

end Deriv
end YM.Work.B02
