import YM.RG.Activities

/-! Internal summability checks. These consume precisely the level caps;
they do not construct either cap. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG
open Lattice MeasureTheory Wilson
open scoped Topology Matrix.Norms.Frobenius

/-- Helper, for accountable application of absolute budgets. -/
def Dominated {ι V X : Type*} [Norm X] (F : ι → V → X) := ∃ B : ι → ℝ,
    Summable B ∧ ∀ i v, ‖F i v‖ ≤ B i

namespace Dominated
variable {ι V X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
variable {F : ι → V → X}

omit [CompleteSpace X] in
theorem absolute (h : Dominated F) (v : V) : Summable fun i => ‖F i v‖ := by
  obtain ⟨B,H,hb⟩ := h
  exact H.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun i => hb i v)

theorem summable (h : Dominated F) (v : V) : Summable fun i => F i v := (h.absolute v).of_norm

-- Keep completeness in the signature, so F is indeed summable.
set_option linter.unusedSectionVars false in
theorem bound (h : Dominated F) : ∃ C : ℝ, ∀ v, ‖∑' i, F i v‖ ≤ C := by
  obtain ⟨B,H,hb⟩ := h
  have hs (v : V) : Summable fun i => ‖F i v‖ := absolute ⟨B,H,hb⟩ v
  exact ⟨_, fun v ↦ (norm_tsum_le_tsum_norm (hs v)).trans ((hs v).tsum_le_tsum (fun i => hb i v) H)⟩
end Dominated

namespace Activities
variable {n : Side} {G : Gauge}
variable {A : Activities G n} {p : BudgetPoint} {δ w : ℝ}

lemma summable_charge {a : ℕ → Support n} (ha : ∀ i, (a i).Nonempty)
    {b : ℕ → ℝ} (hb : ∀ i, 0 ≤ b i)
    (hB : ∀ x, SumBudget (fun i => if x ∈ a i then p.mass (a i) (b i) else 0) w) : Summable b := by
  let q (x : Site n) i := if x ∈ a i then p.mass (a i) (b i) else 0
  apply Summable.of_nonneg_of_le (f := fun i => ∑ x, q x i) hb
  · intro i
    obtain ⟨x,hx⟩ := ha i
    have h : q x i ≤ ∑ y, q y i := Finset.single_le_sum
      (fun y _ ↦ (hB y).1 i) (Finset.mem_univ x)
    exact (p.loMass (a i) (b i) (hb i)).trans (by simpa only [q, if_pos hx] using h)
  refine summable_sum fun i _ ↦ (hB i).2.1

theorem K_total (H : A.KBound p w) : ∃ b : ℕ → ℝ,
    Summable b ∧ ∀ i, 0 ≤ b i ∧ ∀ U, ‖A.K i U‖ ≤ b i := by
  obtain ⟨b,H₁,H₂⟩ := H
  exact ⟨b, summable_charge (fun i => (A.forced i).inventory_ne.mono (A.forced i).inventory_sup)
    (fun i => (H₁ i).1) H₂, H₁⟩

theorem gasSeries (H : A.Valid p δ w) : Dominated (A.gasOccurrence p) := by
  obtain ⟨b,hb,h⟩ := K_total H.boundK
  refine ⟨fun t => ∏ i ∈ t, b i, summable_finsetProd_of_summable_nonneg (fun i => (h i).1) hb, ?_⟩
  intro i v
  unfold gasOccurrence
  split
  · rw [norm_prod]; exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun k _ ↦ (h k).2 _)
  rw [norm_zero]; exact Finset.prod_nonneg fun k _ ↦ (h k).1

theorem E_total (H : A.EBound p δ) : ∃ b : ℕ → ℝ,
    Summable b ∧ ∀ i, p.supBounds (A.reg i).site (A.reg i).support (A.E i) (b i) := by
  obtain ⟨b,H,h⟩ := H
  refine ⟨b, ?_,H⟩
  let q (x : Site n) i := if (A.reg i).site = x then p.mass (A.reg i).support (b i) else 0
  refine Summable.of_nonneg_of_le (f := fun i => ∑ x, q x i) (fun i ↦ (H i).1) ?_ ?_
  · intro i
    simp only [q, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact p.loMass _ _ (H i).1
  exact summable_sum fun i _ => (h i).2.1

theorem ESeries (H : A.Valid p δ w) : Dominated (A.regularOccurrence p) := by
  obtain ⟨b,hb,h⟩ := E_total H.boundE
  refine ⟨b,hb, fun i U ↦ ?_⟩
  by_cases hh : Healthy p.threshold (A.reg i).support U
  · rw [regularOccurrence, masked_eq _ _ _ _ hh]
    exact (h i).2 U hh [] (Nat.zero_le _) (by simp)
  · rw [regularOccurrence, masked_ne _ _ _ _ hh, norm_zero]; exact (h i).1

theorem gas_measurable (H : A.ForcedFamily p) : Measurable (A.gas p) := by
  classical
  unfold gas
  refine Measurable.tsum (fun i ↦ ?_)
  exact Measurable.ite (A.admissible_borel p i) (Finset.measurable_fun_prod _ fun i _ ↦ H.meas i) measurable_const

theorem E_measurable (H : A.RegularFamily p) : Measurable (A.additive p) := by
  unfold additive
  exact Measurable.tsum fun i => masked_measurable _ _ (A.E i) (H.smooth i).borel
end Activities
end YM.RG
