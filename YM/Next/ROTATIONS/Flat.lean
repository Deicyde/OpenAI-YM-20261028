import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Compactification.OnePoint.Basic
import YM.Heat.Rows
import YM.Mink.Poincare
/-! # Jet cancellation estimates. -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Metric
open scoped Topology ContDiff BigOperators NNReal ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- True order. Requires lower jets `k ≤ j < k + m`, uses exactly top derivative cap. -/
theorem under (f : E→F) (hf : ContDiff ℝ ∞ f) (k m : ℕ)
    (h : ∀ j : ℕ,k≤j → j<k+m → iteratedFDeriv ℝ j f 0=0) (r C : ℝ) (hC : 0≤C)
    (hp : ∀ x, ‖x‖ ≤ r → ‖iteratedFDeriv ℝ (k+m) f x‖ ≤ C) (x) (hx : ‖x‖ ≤ r) : ‖iteratedFDeriv ℝ k f x‖ ≤ C*‖x‖^m := by
  induction m generalizing k x with
  | zero => simpa using hp x hx
  | succ m ih =>
    have H : ∀ y∈closedBall 0 ‖x‖, ‖fderiv ℝ (iteratedFDeriv ℝ k f) y‖ ≤ C*‖x‖^m := by
      intro y hy
      have ht : ‖y‖≤‖x‖ := by simpa using mem_closedBall'.mp hy
      rw [norm_fderiv_iteratedFDeriv]
      exact (ih (k+1) (fun j a b => h j (by omega) (by omega)) (by rw [show k+1+m=k+(m+1) by omega]; exact hp)
        y (ht.trans hx)).trans (by gcongr)
    have hw := Convex.norm_image_sub_le_of_norm_fderiv_le (s:=closedBall 0 ‖x‖) (x:=0) (y:=x)
      (fun y _ => hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top k) y) H (convex_closedBall ..) (by simp) (by simp)
    simpa only [h k le_rfl (by omega),sub_zero,pow_succ,mul_assoc] using hw

theorem earnings [ProperSpace E] (f : E→F) (hf : ContDiff ℝ ∞ f) (k m : ℕ)
    (h : ∀ j : ℕ,k≤j → j<k+m → iteratedFDeriv ℝ j f 0=0) (r : ℝ) : ∃ C : ℝ, 0≤C ∧ ∀ x, ‖x‖≤r →
      ‖iteratedFDeriv ℝ k f x‖ ≤ C*‖x‖^m := by
  have hc : Continuous (iteratedFDeriv ℝ (k+m) f) := hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E) r).bddAbove_image hc.norm.continuousOn
  refine ⟨max 0 C,le_max_left ..,under f hf k m h r _ (le_max_left ..) fun x hx => ?_⟩
  exact le_trans (b:=C) (hC (mem_image_of_mem _ (show x∈closedBall 0 r from by simpa using hx))) (le_max_right ..)
end YM.Outer
