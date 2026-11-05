import YM.RG.Block

/-! Exact masses and signed coefficient push. This is why mesh data
use the same vacuum scalar in every insertion.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG.StepData

open MeasureTheory Lattice Wilson Filter
open scoped Topology Matrix.Norms.Frobenius ENNReal
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {c f : Side} {S : StepData c f} {G : Gauge} {β : ℝ}

/-- Each slice used, not merely almost every slice. -/
theorem push_slice (h : S.IsKernel β G) (V : Config G c) (F : Config G f → X)
    (hf : Integrable F (prior G f)) : Integrable (fun x => S.density β x V • F x) (prior G f) := by
  obtain ⟨C,H⟩ := h.bound
  have he : Measurable fun x => S.density β x V := by
    change Measurable ((fun p : Config G f × Config G c => S.density β p.1 p.2) ∘ fun x => (x,V))
    exact h.meas.comp (measurable_id.prodMk measurable_const)
  apply hf.bdd_smul C he.aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ (Real.norm_of_nonneg (h.positive x V)).trans_le (H x V)

theorem push_integrand (h : S.IsKernel β G) (F : Config G f → X)
    (hf : Integrable F (prior G f)) : Integrable
      (fun p : Config G f × Config G c => S.density β p.1 p.2 • F p.1) ((prior G f).prod (prior G c)) := by
  obtain ⟨C,H⟩ := h.bound
  apply (hf.comp_fst _).bdd_smul C h.meas.aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ (Real.norm_of_nonneg (h.positive x.1 x.2)).trans_le (H x.1 x.2)

theorem push_integrable (h : S.IsKernel β G) (F : Config G f → X)
    (hf : Integrable F (prior G f)) : Integrable (S.push β F) (prior G c) :=
  (push_integrand h F hf).integral_prod_right

theorem push_integral [CompleteSpace X] (h : S.IsKernel β G) (F : Config G f → X)
    (hf : Integrable F (prior G f)) :
    (∫ V, S.push β F V ∂prior G c) = ∫ x, F x ∂prior G f := by
  unfold push
  rw [← integral_integral_swap (μ := prior G f) (ν := prior G c)
    (f := fun x V => S.density β x V • F x) (push_integrand h F hf)]
  simp_rw [integral_smul_const, h.total, one_smul]

theorem push_add (h : S.IsKernel β G) (F F' : Config G f → X)
    (hf : Integrable F (prior G f)) (hf' : Integrable F' (prior G f)) :
    S.push β (F+F') = S.push β F + S.push β F' := by
  funext i
  simp only [push, Pi.add_apply, smul_add]
  rw [integral_add (push_slice h i F hf) (push_slice h i F' hf')]

theorem push_smul (S : StepData c f) (F : Config G f → ℂ) (β : ℝ) (z : ℂ)
    (_ : Integrable F (prior G f)) : S.push β (z • F) = z • S.push β F := by
  funext i
  simp only [push, Pi.smul_apply, smul_comm _ z, integral_smul]
end YM.RG.StepData
