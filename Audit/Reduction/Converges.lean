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
  sorry

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
  sorry

end YMAudit
