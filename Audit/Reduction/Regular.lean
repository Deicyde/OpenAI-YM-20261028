import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The gauge-blind family satisfies every clause of `WilsonRegularity`. -/
theorem blind_regular {g : GaugeGroup} (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (F : ℕ → Type) [∀ d, Zero (F d)] :
    WilsonRegularity (blindFamily μ hH F) := by
  refine ⟨⟨1, one_pos, fun ε hε => Eventually.of_forall fun N p => ?_⟩,
    fun _ _ _ _ => continuous_const, fun _ _ _ _ _ _ => rfl,
    fun _ => ⟨∅, fun _ _ _ => by intro sites U V _; rfl⟩⟩
  have hpos : 0 < Real.log ((N + 2 : ℕ) : ℝ) := Real.log_pos (by norm_cast; omega)
  have hd : (blindFamily μ hH F).beta N p / Real.log ((blindFamily μ hH F).mesh N)⁻¹ = 1 := by
    show Real.log ((N + 2 : ℕ) : ℝ) / Real.log ((((N + 2 : ℕ) : ℝ))⁻¹)⁻¹ = 1
    rw [inv_inv, div_self hpos.ne']
  rw [hd, sub_self, abs_zero]
  exact hε

end YMAudit
