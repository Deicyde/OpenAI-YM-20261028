import YM.WilsonBulk.Grid.Moment

/-! Checking budget in dual tests (finite sign options) allows taking Taylor bounds from ordinary
scalar derivatives, no interpolation/dimension cost. -/
namespace YM.WilsonBulk
noncomputable section
open Lattice Laurent Filter Function Bloch
open Push.AbsoluteSums RG Finset Work.F08
open scoped Topology BigOperators Classical

-- reusable for asymmetric/multimesh/root norms too
lemma budget_dual {ι : Type*} {f w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {c : ℝ}
    (h : ∀ (s : Finset ι) (g : ι → ℝ), (∀ i∈s, ‖g i‖ ≤ w i) → ‖∑ i∈s, f i * g i‖ ≤ c) :
    SumBudget (fun i => w i * ‖f i‖) c := by
  refine budget_of_sum (fun i => mul_nonneg (hw i) (norm_nonneg _)) fun s => ?_
  let g i := if 0 ≤ f i then w i else - w i
  have he i : ‖g i‖ = w i := by dsimp only [g]; split <;> simp [Real.norm_of_nonneg (hw _)]
  have hf i : f i * g i = w i * ‖f i‖ := by
    dsimp only [g]; split <;> rename_i h
    · simp [Real.norm_of_nonneg h,mul_comm]
    simp [Real.norm_eq_abs, abs_of_neg (lt_of_not_ge h),mul_comm]
  have hm := h s g fun i _ => (he i).le
  simp_rw [hf] at hm
  rw [Real.norm_of_nonneg] at hm
  · exact hm
  exact sum_nonneg fun i _ => mul_nonneg (hw i) (norm_nonneg _)

lemma via_dual {f : Cover→ℝ} {c σ : ℝ}
    (h : ∀ (s : Finset Cover) (p : Cover → ℝ), (∀ i∈s, ‖p i‖ ≤ Real.exp (σ*span i)) → ‖∑ i∈s, f i * p i‖ ≤ c) :
    Width σ c f := budget_dual (fun _ => (Real.exp_pos _).le) h

end
end YM.WilsonBulk
