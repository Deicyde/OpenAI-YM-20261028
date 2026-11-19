import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- A compactly supported test eventually fits in the box of every large volume. -/
theorem eventually_suitable {g : GaugeGroup} (C : WilsonFamily g) {order : ℕ → ℕ}
    (ho : StrictMono order) {n : ℕ} (t : WilsonFamily.SeparatedTest n) :
    ∀ᶠ k in atTop, C.suitable (order k) t := by
  have hK : IsCompact (tsupport t) := t.hasCompactSupport
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine Filter.eventually_atTop.2 ⟨⌈2 * R⌉₊ + 1, fun k hk => ?_⟩
  intro x hx i a
  have h1 : |x i a| ≤ R :=
    calc |x i a| = ‖x i a‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x i‖ := PiLp.norm_apply_le (x i) a
      _ ≤ ‖x‖ := PiLp.norm_apply_le x i
      _ ≤ R := hR x hx
  have h2 : (k : ℝ) ≤ ((C.period (order k)).val : ℝ) := by
    have hk1 : k ≤ order k := ho.le_apply
    have hk2 : order k ≤ (C.period (order k)).val := C.periodStrict.le_apply
    exact_mod_cast hk1.trans hk2
  have h3 : 2 * R < k := by
    have hc := Nat.le_ceil (2 * R)
    have hk' : ((⌈2 * R⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at hk'
    linarith
  have h4 := neg_abs_le (x i a)
  have h5 := le_abs_self (x i a)
  constructor <;> linarith

/-- The gauge-blind family converges, along any strictly increasing volume order, to the
indicator `allZero`, given the moment identity and the Riemann-sum limit. -/
theorem blind_converges {g : GaugeGroup} (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (F : ℕ → Type) [∀ d, Zero (F d)] {order : ℕ → ℕ}
    (ho : StrictMono order)
    (hmoment : ∀ (N p : ℕ) {n : ℕ} (v : Fin n → Σ d, F d)
      (x : Fin n → Site ((blindFamily μ hH F).period p * (blindFamily μ hH F).denominator N)),
      (blindFamily μ hH F).finiteMoment N p v x = allZero v)
    (hriemann : ∀ (p : ℕ) {n : ℕ} (t : WilsonFamily.SeparatedTest n),
      (blindFamily μ hH F).suitable p t →
      Tendsto (fun N => ((blindFamily μ hH F).mesh N : ℂ) ^ (4 * n) *
          ∑ x : Fin n → Site ((blindFamily μ hH F).period p * (blindFamily μ hH F).denominator N),
            t (WithLp.toLp 2 fun i => (blindFamily μ hH F).place N p (x i)))
        atTop (𝓝 (∫ x, t x))) :
    (blindFamily μ hH F).Converges order (fun v _ => allZero v) := by
  intro n v t
  refine ⟨eventually_suitable _ ho t, fun _ => (∫ x, t x) * allZero v, fun p hp => ?_, ?_⟩
  · have key : ∀ N, (blindFamily μ hH F).smear N p v t =
        (((blindFamily μ hH F).mesh N : ℂ) ^ (4 * n) *
          ∑ x : Fin n → Site ((blindFamily μ hH F).period p * (blindFamily μ hH F).denominator N),
            t (WithLp.toLp 2 fun i => (blindFamily μ hH F).place N p (x i))) * allZero v := by
      intro N
      simp only [WilsonFamily.smear, hmoment, Finset.sum_mul, mul_assoc]
    simp only [key]
    exact (hriemann p t hp).mul_const _
  · simp only [integral_mul_const]
    exact tendsto_const_nhds

end YMAudit
