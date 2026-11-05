import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Push.LOOP_COEFFICIENT.Envelope

/-!
# Comparing alias counting weights with q factors
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Kernel
open Complex Function Filter Set Lattice Laurent Bloch Exterior Metric
open scoped Topology BigOperators
variable {z : ℂ} {p : Momentum} {L : Side} {η : ℝ}



lemma alias_real (l : Site L) (p : Momentum) (i : Axis) : (aliasAt p l i).re = ((p i).re + 2*Real.pi*(Lattice.lift l i:ℤ)) / L.val := by
  rw [aliasAt,mon,← smul_add]; simp [Pi.smul_apply, smul_eq_mul, reciprocal, inv_mul_eq_div]
lemma alias_core (h : Odd L.val) (l : Site L) (hp : p∈Center η) (i : Axis) : |(aliasAt p l i).re| ≤ Real.pi := by
  obtain ⟨k,hk⟩ := h
  obtain ⟨h₁,h₂⟩ := lift_centers l i
  have he : ((-(k:ℤ) ≤ Lattice.lift l i) ∧ (Lattice.lift l i ≤ k)) := by omega
  have hr : (-(k:ℝ) ≤ ((Lattice.lift l i:ℤ):ℝ)) ∧ (((Lattice.lift l i :ℤ):ℝ) ≤ k) := by exact_mod_cast he
  rw [alias_real, abs_le, le_div_iff₀ (side_pos L),div_le_iff₀ (side_pos L),hk]; push_cast
  have ht := abs_le.mp (hp.2 i)
  constructor <;> nlinarith [Real.pi_pos]

end YM.Push.Loops.Kernel
