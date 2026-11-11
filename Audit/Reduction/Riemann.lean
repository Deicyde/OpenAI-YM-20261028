import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Riemann sums: for any Wilson family and any separated test supported in the open box of
side `period p`, the lattice sums used by `smear` converge to the integral. -/
theorem riemann_tendsto {g : GaugeGroup} (C : WilsonFamily g) (p : ℕ) {n : ℕ}
    (t : WilsonFamily.SeparatedTest n) (ht : C.suitable p t) :
    Tendsto (fun N => (C.mesh N : ℂ) ^ (4 * n) *
        ∑ x : Fin n → Site (C.period p * C.denominator N),
          t (WithLp.toLp 2 fun i => C.place N p (x i)))
      atTop (𝓝 (∫ x, t x)) := by
  sorry

end YMAudit
