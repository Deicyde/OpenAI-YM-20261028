import YM.Further.DENSE_MIXED_KERNELS.Throng
import YM.Further.DENSE_MIXED_KERNELS.View
import YM.SectorNext.VACUUM_NORMALIZATION.Covered


/-!
# A way to retain the genuine unmarked K partners in a dense assembly

They can stay summed, e.g. when X is a mandatory packet already carrying
*all* V sites. Accounts the input K sum relative to actual Rep, parameters
at this N: no convergence assumptions besides true budgets. Caller still
selects compatible MARKED data (one variant per actual gas label), bills
Ink on that. Provisional responses along the same sector. Structural assumptions in pricing
in the log etc must use corresponding data. Don't use when altering/dropping
support restrictions of less-than-full labels. This variant of budgeting
would lose sharp estimates if trying to transfer defect over regions where
the input support is local!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Finset Lattice RG Wilson Pressure Precision Module Tree
open Push.SectorMeasure Next.Fluctuations.Sector Push.AbsoluteSums Corona Overlay Labels Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {n : Side} {G : Gauge} {R : Rep G n} {σ C Λ δ w : ℝ} {J : Finset ℕ}
    {V : Type} [DecidableEq V] {L : Census V} {A : Bands L R} {U : Config G n}

namespace Throng
-- include original compatibilities/sum before looking at a mark

def pay (R : Rep G n) (J k : Finset ℕ) (U : Config G n) := if Disjoint J k ∧ R.activities.admissible R.p U (J∪k) then
      ∏ i∈k,R.activities.K i U else 0
def waiting (R : Rep G n) (J : Finset ℕ) (U : Config G n) : ℝ := ∑' k,pay R J k U

theorem absolute (h : R.Lawful σ C Λ δ w) (J : Finset ℕ) : ∃ v : Finset ℕ → ℝ,
    (∀ k U,Measurable (pay R J k) ∧ ‖pay R J k U‖ ≤ v k) ∧
    SumBudget v (Real.exp (Fintype.card (Site n)*w)) := by
  obtain ⟨f,hf,hB⟩ := h.labels.boundK
  have hv i : 0≤f i := (hf i).1
  have hg i : (R.activities.forced i).support.Nonempty := (R.activities.forced i).inventory_ne.mono
    (R.activities.forced i).inventory_sup
  have hs : Summable f := Activities.summable_charge hg hv hB
  let c (l : Finset ℕ) := ∏ i∈l, f i
  have hz i : 0≤c i := prod_nonneg fun j _ => hv j
  refine ⟨c, fun k U => ⟨?_,?_⟩,hz, summable_finsetProd_of_summable_nonneg hv hs,
    (SectorNext.Vacuum.sum_exp_bound f hv hs).trans (Real.exp_monotone (sumRoot hg hv hB))⟩
  · unfold pay; by_cases he : Disjoint J k
    · simp_rw [he,true_and]; exact Measurable.ite (R.activities.admissible_borel R.p _) (Finset.measurable_fun_prod k
        fun i _ => h.labels.forced.meas i) measurable_const
    simp only [he,false_and,↓reduceIte]; exact measurable_const
  unfold pay; split
  · rw [norm_prod]; exact prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (hf i).2 _
  rw [norm_zero]; exact hz _

lemma preserved (h : R.Lawful σ C Λ δ w) (U : Config G n) : Summable (fun k => ‖pay R J k U‖) ∧
    ‖waiting R J U‖ ≤ Real.exp (Fintype.card (Site n)*w) := by
  obtain ⟨v,hv,h⟩ := absolute h J
  have hs := h.2.1.of_nonneg_of_le (fun i => norm_nonneg (pay R J i U)) (fun i => (hv i U).2)
  exact ⟨hs, (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum (fun i => (hv i U).2) h.2.1).trans h.2.2)⟩
lemma env (h : R.Lawful σ C Λ δ w) (J : Finset ℕ) : Envelope (waiting R J) := by
  obtain ⟨v,hv,-⟩ := absolute h J
  exact ⟨Measurable.tsum fun i => (hv i (1:Config G n)).1,_,fun U => (preserved h U).2⟩

/-- The marked understanding of a gas selection. For J and menu representing
ONE real mark term (don't try writing two onto a K label). Multiplying
coefficients of the same surviving monomial is checked against these addresses
separately. We keep an exact sum of literal selection values, zero if
coverage fails anywhere. -/
def order (A : Bands L R) (J : Finset ℕ) (recipe : ℕ→ℕ) (K : Finset ℕ) (U : Config G n) :=
    if Disjoint J K ∧ R.activities.admissible R.p U (J∪K) then
      (∏ i∈J,A.entries i (recipe i) U)*(↑(∏ i∈K, R.activities.K i U):ℂ) else 0


-- coverage with exact K owners at these histories (address has inventories incl ghost entries)

end Throng
end YM.Further.DenseMixedKernels
