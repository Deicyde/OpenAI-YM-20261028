import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Grant

/-!
# Keep the incoming flags through the annulus payment

Use only choices with the  incidence and show the exact formula
at every b term. This file about the eligibility/prerequisite and gas
occurrence; we do not need a particular masking of other analytic E
addresses to prove the bounds later. Mark everything tested including
at original support, outside void factors still see their own flag halos.
No claim of K locality or its costs off these prerequisites.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Dress
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix

open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented LabelSum Presented

open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

variable (A : Activities G f) (p : BudgetPoint) (b : Finset ℕ) (U : Config G f)

def blanket := b.biUnion fun i => (A.forced i).support

/-- qvoid, not to confuse with the Chi on the Allocation. -/
def freeTest (R : Finset (Site f)) :=
  ∏ i ∈ R, if (i ∉ blanket A b → i ∉ RG.flags p.threshold U) then (1:ℝ) else 0









lemma stamps (R : Finset (Site f)) : freeTest A p b U R=1 ∨ freeTest A p b U R=0 := by
  classical
  by_cases H : ∀ i∈R,i∉blanket A b → i∉RG.flags p.threshold U
  · left; apply Finset.prod_eq_one; intro i hi; exact if_pos (H i hi)
  right
  by_contra! he; apply H
  intro i hi; have h := Finset.prod_ne_zero_iff.mp he i hi
  change (if i∉_ → i∉_ then (1:ℝ) else 0) ≠ 0 at h
  split at h; assumption; exact (h rfl).elim

lemma stamp_meas (R : Finset (Site f)) : Measurable (fun U : Config G f => freeTest A p b U R) := by
  apply Finset.measurable_fun_prod
  intro i hi
  by_cases h : i ∉ blanket A b
  · simp only [h,not_false_eq_true,true_implies]
    exact Measurable.ite (RG.flags_open i _ |>.measurableSet.compl) measurable_const measurable_const
  push Not at h; simpa only [h,not_true_eq_false,false_implies,↓reduceIte] using (measurable_const (a:=(1:ℝ)) : @Measurable (Config G f) _ _ _ _)









/-- Support tested for E qvoid in the Packet, including where suppressed
by K. Does not bound the region needed to access all data for that K. -/
def openedHere (O : Stores S) (R : ℕ) := Finset.univ.filter fun i => S.ratio.parent i ∈ O.dome R
def examine (O : Stores S) (R : ℕ) := freeTest A p b U (openedHere O R)

lemma examine_range (O : Stores S) (R : ℕ) : examine A p b U O R ∈ Set.Icc (0:ℝ) 1 := by
  unfold examine; rcases stamps A p b U (openedHere O R) with h|h <;> rw [h] <;> simp

end YM.AnalyticBridge.AnnulusRatioInsertions.Dress
