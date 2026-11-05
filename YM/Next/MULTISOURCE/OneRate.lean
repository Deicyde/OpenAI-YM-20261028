import YM.Next.MULTISOURCE.LevelD

/-! qualify references during diagnostic. k=0 allowed! -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Wilson Lattice MeasureTheory Marker Function Filter Finset Single
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} (C : Family G) {d N p j : ℕ}







section
variable {P : BudgetPoint} {n : Side} {X : Support n} {r K k : ℝ} (D : Pulse G n)
def normalize (D : Pulse G n) (k : ℝ) : Pulse G n := (k:ℂ)⁻¹ • D
lemma normalizeCredit (h : Credit P r K X D k) : Credit P r K X (normalize D k) 1 ∧ D = (k:ℂ) • normalize D k := by
  by_cases he : k=0
  · have he' : D=0 := by
      apply Prod.ext
      · funext U; apply norm_le_zero_iff.mp; simpa [he] using (personal h).2.2.1 U
      funext i U; apply norm_le_zero_iff.mp; simpa [he] using (personal h).2.2.2 i U
    simp only [normalize,he, he', Complex.ofReal_zero, smul_zero]; exact ⟨by
      rw [← he']; exact h.expand (he.trans_le zero_le_one), trivial⟩
  constructor
  · apply Credit.expand (h.scale _); rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg h.2.2.2.1,
      inv_mul_cancel₀ he]
  exact (smul_inv_smul₀ (by exact_mod_cast he : (k:ℂ)≠0) D).symm
end
end YM.Multi.Step
