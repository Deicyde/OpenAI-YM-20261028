import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Packets


/-!
# Local multiplier incomes under the envelope loads

Y held on probability measure. Actual real Z color array. Suppression
from a combined trigger only used on the same Z. In particular no
independence even of triggered ends. And the simultaneous moment doesn't
charge the full size of the axial hull with a fixed constant per variable.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Capacitor
open Filter Function MeasureTheory Finset Matrix
open Next.SectorChange.Gaussian Next.SectorChange
open scoped Topology BigOperators Classical ENNReal

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I]

/-- E letters with coefficient already priced. L¹ below can absorb much
rougher extensions than quadratics if the same growth check holds. -/
lemma charge (a q x : ℝ) (hq : 0 ≤ q) (hx : x ∈ Set.Icc (0:ℝ) 1) (h : |a| ≤ x^2*q) :
    |Real.exp a-1| ≤ x*Real.exp (2*x*q) := by
  have he : |Real.exp a-1| ≤ |a| * Real.exp |a| := by
    rcases le_total 0 a with hf|hf
    · rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hf)),abs_of_nonneg hf]
      have hg := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-a)) (Real.exp_pos a).le
      rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hg; linarith only [hg]
    rw [abs_of_nonpos hf,abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hf))]
    linarith only [Real.add_one_le_exp a, le_mul_of_one_le_right (show 0 ≤ -a from neg_nonneg.mpr hf)
      (Real.one_le_exp (neg_nonneg.mpr hf))]
  obtain ⟨hp,hk⟩ := hx
  have h₁ : x^2 * q ≤ x * q := mul_le_mul_of_nonneg_right (by nlinarith) hq
  calc
    _ ≤ _ := he
    _ ≤ (x^2*q) * Real.exp (x*q) := mul_le_mul h (Real.exp_monotone (h.trans h₁)) (Real.exp_pos _).le (by positivity)
    _ ≤ (x * Real.exp (x*q)) * Real.exp (x*q) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have hh := mul_le_mul_of_nonneg_left (show x*q ≤ Real.exp (x*q) by linarith only [Real.add_one_le_exp (x*q)]) hp
      linarith only [hh]
    _ = _ := by rw [mul_assoc,← Real.exp_add]; ring_nf

/-- `line i j`: all test multiplicity at the corresponding *real
coordinate*. Need same including both endpoints as many times as read.
Weights `x` like square roots of coefficient bounds. `Q` aggregate of
simultaneous distinct events at THIS sample (no payment once per
occurrence using the same rare event). -/
structure Card (I J : Type) where
  x : I → ℝ
  range i : x i ∈ Set.Icc (0:ℝ) 1
  line : I → Vec J
  ink i j : 0 ≤ line i j
  Q : Vec J
  pos j : 0 ≤ Q j

namespace Card

variable (R : Card I J) (s : Finset I) (n : ℕ)















variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]


end Card
end YM.AnalyticBridge.Sharp.Capacitor
