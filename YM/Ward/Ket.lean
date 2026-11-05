import YM.Hilbert.Kolmogorov
import YM.Ward.Rate




/-!
# Hilbert line analyticity. Transverse growth suffices from transported
pair jets at a point via translations. Weak identities against arbitrary
other plants across CONF; don't need Gram higher mixed derivatives supplied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Analysis
open Function Set Filter MeasureTheory Measure
open scoped Topology ContDiff BigOperators InnerProductSpace

variable {X : Type} {K : X → X → ℂ}
lemma represents (S : Kernel.Gram K) (f g : ℝ → S.H) (hg : Continuous g)
    (h : ∀ x : X, ∀ t, HasDerivAt (fun y => inner ℂ (S.plant x) (f y)) (inner ℂ (S.plant x) (g t)) t) (x : ℝ) :
    HasDerivAt f (g x) x := by
  suffices he : f = fun t => f 0 + ∫ y in (0:ℝ)..t, g y by
    nth_rw 1 [he]
    apply HasDerivAt.const_add
    exact intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 x)
      hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  funext t
  apply eq_add_of_sub_eq'
  let z := ∫ y in (0:ℝ)..t, g y
  have ht (i : X) : inner ℂ (S.plant i) (f t-f 0) = inner ℂ (S.plant i) z := by
    let V : S.H →L[ℂ] ℂ := innerSL ℂ (S.plant i)
    have he := V.intervalIntegral_comp_comm (hg.intervalIntegrable (μ := volume) 0 t)
    unfold z; rw [inner_sub_right]
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => h i y)
      ((V.continuous.comp hg).intervalIntegrable 0 t)).symm.trans he
  apply S.whole.eq_of_inner_right ℂ
  intro p
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add,inner_add_left,hu,hv]
  | single i c => simp [Kernel.Gram.stems,inner_smul_left,z] at *; rw [ht]; exact Or.inl rfl

variable {H : Hilbert} (f : ℝ → H)

/-- This is actual smooth trajectory. -/
lemma bud (h : ContDiff ℝ ∞ f) (x t : ℝ) (A : ℝ → ℂ)
    (hv : ∀ (x t : ℝ), inner ℂ (f x) (f t)=A (t-x)) (k m : ℕ) :
    inner ℂ (iteratedDeriv m f x) (iteratedDeriv k f t) = (-1:ℂ)^m * iteratedDeriv (k+m) A (t-x) := by
  have He n y : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f y) y := by
    rw [iteratedDeriv_succ]; exact ((h.differentiable_iteratedDeriv
        (m := n) (show n < (∞:WithTop ℕ∞) from WithTop.coe_lt_coe.mpr (by simp))) y).hasDerivAt
  have hA : ContDiff ℝ ∞ A := by
    have ht : A=fun t => inner ℂ (f 0) (f t) := funext fun i => by rw [hv,sub_zero]
    rw [ht]; exact contDiff_const.inner ℂ h
  have Ha n y : HasDerivAt (iteratedDeriv n A) (iteratedDeriv (n+1) A y) y := by
    rw [iteratedDeriv_succ]; exact ((hA.differentiable_iteratedDeriv
        (m := n) (show n < (∞:WithTop ℕ∞) from WithTop.coe_lt_coe.mpr (by simp))) y).hasDerivAt
  induction m generalizing x t with
  | zero =>
    induction k generalizing x t with
    | zero => simpa using hv x t
    | succ k ih =>
      simp only [iteratedDeriv_zero,Nat.add_zero,pow_zero,one_mul] at *
      have hh := (hasDerivAt_const (x := t) (f x)).inner ℂ (He k t)
      simp only [inner_zero_left,add_zero,ih] at hh
      have he := (Ha k (t-x)).scomp t ((hasDerivAt_id' t).sub_const x)
      simpa using hh.unique he
  | succ m ih =>
    have hh := (He m x).inner ℂ (hasDerivAt_const _ (iteratedDeriv k f t))
    rw [inner_zero_right,zero_add] at hh
    simp_rw [ih] at hh -- rewrite fn only
    have hz := ((Ha (k+m) (t-x)).scomp x ((hasDerivAt_id' x).const_sub t)).const_mul ((-1:ℂ)^m)
    have hx := hh.unique hz
    simpa [pow_succ,Nat.add_assoc] using hx

theorem blossoms (h : ContDiff ℝ ∞ f) (A a : ℝ → ℂ) (ha : AnalyticAt ℝ a 0)
    (hv : ∀ x t, inner ℂ (f x) (f t)=A (t-x)) (ht : ∀ n, iteratedDeriv n A 0=iteratedDeriv n a 0)
    (x : ℝ) : AnalyticAt ℝ f x := by
  obtain ⟨C,hc,ρ,r,Hb⟩ := center a 0 ha
  apply builds f h (√C) (ρ/2) (by positivity) (by positivity) _ x
  intro m x
  unfold Power at *
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  have he : ‖iteratedDeriv m f x‖^2 ≤ C*(ρ^(m+m))⁻¹*((m+m).factorial:ℝ) := by
    have he := congr_arg norm (bud f h x x A hv m m)
    simp [inner_self_eq_norm_sq_to_K,ht] at he
    rw [he]; exact Hb _
  apply he.trans
  have Hh : (m+m).factorial ≤ 2^(m+m)*m.factorial^2 := by
    calc _ = (m+m).choose m * m.factorial * m.factorial := by rw [← Nat.choose_mul_factorial_mul_factorial (show m≤m+m by omega),Nat.add_sub_cancel_left]
         _ ≤ _ := by rw [pow_two,← mul_assoc];gcongr; exact Nat.choose_le_two_pow ..
  calc _ ≤ C * (ρ^(m+m))⁻¹ * (2^(m+m)*(m.factorial:ℝ)^2) := by gcongr; exact_mod_cast Hh
       _ = _ := by
        rw [mul_pow, mul_pow (√C),Real.sq_sqrt hc.le]
        simp only [pow_add,div_pow, inv_div] -- simplified?
        field_simp
end YM.Analysis
