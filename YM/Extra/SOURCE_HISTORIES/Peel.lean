import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Extra.SOURCE_HISTORIES.Motion
import YM.Next.FOUNDATIONS.Split

/-!
# Absolute multiplier receipts under FLUCTUATIONS grant

Can carry our same source columns along the FLUCTUATIONS sector bound,
keeping actual masks & support. For *unintegrated factors* (unit, masked
primary, masked REGULAR terms, and K replacing a K occurrence -- NOT
including all the rest of a forced or vacuum product in the budget!), true
supports still needed. Source bill in absolute value, doesn't assume any
independence from branch choice. Compare on actual common tags with FLUC
cut crown term kept and probability Haar prefactor, and free an extra
nonnegative integrable multiplier even *tag-dependent*, so e.g. a caller
can keep the other factors required by a branch. Does not supply their size
or integrability. This is an actual inequality *when* assessing with this
peeled integrand; not a proof that the Pencil step already has this form
with no other factors/restoration, nor the red AtomStep estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Peel
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
variable (B : SectionData F) (R : Rep G n) (P : Coefficient F n)
variable (o : Site n)

def primaryCut := masked R.p.threshold (B.footprint o) (B.places (F.scaled R.p.threshold⁻¹ (F.core P.x)) o)

/-- `v` the positive κ divisor of a `remBound`. -/

def till (v : ℝ) (U : Config G n) := (‖P.x 0‖ + ‖primaryCut B R P o U‖ +
    (∑' i : ℕ, ‖P.maskedTerm R i U‖)) + (∑' i : ℕ, ‖P.forced i U‖)/v

def prize {F : Labels.Frame G d} {n : Side} (t a : ℝ) (P : Coefficient F n) :=
    ‖P.x 0‖+a*F.coeffSize (F.core P.x)+t

/-- Explicit l1 upper (no volume losses); caller applying to PAPER
input uses its actual RefLi.Credit for B. -/
theorem ticket {A : Hol G} {v t a : ℝ} (hp : P.Format o A R) (ht : P.remBound o R v t)
    (hB : Bid.Credit B R.p.order R.p.power a) :
    Measurable (till B R P o v) ∧ ∀ U, 0 ≤ till B R P o v U ∧ till B R P o v U ≤ prize t a P := by
  refine ⟨?_,fun U => ?_⟩
  · unfold till
    refine ((measurable_const.add ((masked_measurable _ _ _ (B.continuous_places ..).measurable).norm)).add
      (Measurable.tsum fun i => (masked_measurable _ _ _ (hp.smooth i).borel).norm)).add
        ((Measurable.tsum fun i => (hp.borel i).norm).div_const _)
  obtain ⟨I,J,hI,hJ,hr,hv,⟨b,hb,hb'⟩,c,hc,hc'⟩ := ht
  have he i : ‖P.maskedTerm R i U‖ ≤ R.p.mass (P.support i) (b i) := by
    refine le_trans (b:=b i) ?_ (R.p.loMass _ _ (hb' i).1)
    unfold Coefficient.maskedTerm
    by_cases hx : Healthy R.p.threshold (P.support i) U
    · rw [masked_eq _ _ _ _ hx]; exact (hb' i).2 U hx [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hx,norm_zero]; exact (hb' i).1
  have hy i : ‖P.forced i U‖ ≤ R.p.mass (R.activities.forced i).support (c i) :=
    ((hc' i).2 U).trans (R.p.loMass _ _ (hc' i).1)
  have hx : ∑' i, ‖P.maskedTerm R i U‖ ≤ I := (Summable.tsum_le_tsum he (Summable.of_nonneg_of_le
    (fun i => norm_nonneg _) he hb.2.1) hb.2.1).trans hb.2.2
  have hj : (∑' i, ‖P.forced i U‖)/v ≤ J := (div_le_iff₀ hv).mpr ((Summable.tsum_le_tsum hy
    (Summable.of_nonneg_of_le (fun i => norm_nonneg _) hy hc.2.1) hc.2.1).trans (hc.2.2.trans_eq (mul_comm ..)))
  have h0 : ‖primaryCut B R P o U‖ ≤ a*F.coeffSize (F.core P.x) := by
    have hh := (Next.Foundations.combination_bound R.p o hB (F.scaled R.p.threshold⁻¹ (F.core P.x))).2
    rw [Frame.scaled_inv F R.p.threshold_pos.ne'] at hh
    unfold primaryCut
    by_cases hn : Healthy R.p.threshold (B.footprint o) U
    · rw [masked_eq _ _ _ _ hn]; exact hh.2 U hn [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hn,norm_zero]; exact hh.1
  unfold till prize
  exact ⟨by positivity,by linarith⟩

open Tree Supply Pressure Pressure.Stores Pressure.Tube Precision Input  


end YM.Extra.Histories.Peel
