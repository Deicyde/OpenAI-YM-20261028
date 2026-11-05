import YM.Push.FREE_RESOLVENT.Windows
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Windows


/-!
Exact interface between SectorChange.per (set windows, may miss their
anchor) and FreeResolvent.inspect (dependent-index survey, ALWAYS
contains anchor). Keep the column-dependent choice in both entries of a
symmetrization. In particular, using a row from window i when window j
is wanted is *not* licensed. Algebra here in counting coordinates; no
weight conventions or positivity needed, inverse even has its normal
Lean zero default (see the estimates for when used as a real inverse).
No sector, pricing, nor horizon hypothesis yet. u is an energy shift,
not β.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Next SectorChange FreeResolvent Matrix Function
open SectorChange.Gaussian
open scoped Classical BigOperators

variable {ι κ : Type} [Fintype ι] [DecidableEq ι]

/-- columns, arbitrary sets, real energy shift, possibly
invalid self membership (use 0 there as for SectorChange). -/
def pane (W : ι → Set ι) (Q : Gaussian.Table ι) (u : ℝ) : Gaussian.Table ι :=
  SectorChange.Schur.per W (Q + u • 1)

lemma pane_zero (W : ι → Set ι) (Q : Gaussian.Table ι) :
    pane W Q 0 = SectorChange.Schur.per W Q := by simp [pane]

lemma pane_read (W : ι → Set ι) (Q : Gaussian.Table ι) (u : ℝ) {i j}
    (h : i ∈ W i) (e : j ∈ W i) :
    pane W Q u j i = ((SectorChange.Schur.principal Q (W i) + u • 1)⁻¹) ⟨j,e⟩ ⟨i,h⟩ := by
  rw [pane, SectorChange.Schur.per_read _ _ h e, SectorChange.Schur.principal,
    shift_compress _ _ u Subtype.val_injective]
  rfl

lemma pane_absent (W : ι → Set ι) (Q : Gaussian.Table ι) (u : ℝ) {i j}
    (h : i ∉ W i ∨ j ∉ W i) : pane W Q u j i=0 := by
  rcases h with h|h
  · unfold pane SectorChange.Schur.per; rw [Matrix.of_apply,dif_neg h]
  exact SectorChange.Schur.per_zero _ _ h

/-- Endpoint version (and any alternative) at self-containing
radii really gives a FreeResolvent survey. Keep subtype indexing so the
same slots, not all slots of adjacent blocks. -/
def setSurvey (W : ι → Set ι) (h : ∀ i, i ∈ W i) :
    FreeResolvent.Window.Survey (fun i => W i : ι → Type) := {
  loc _ := Function.Embedding.subtype _
  root i := ⟨i,h i⟩
  atRoot _ := rfl }

theorem inspect_sets (W : ι → Set ι) (h : ∀ i, i ∈ W i) (Q : Gaussian.Table ι) (u : ℝ) :
    (setSurvey W h).inspect Q u = pane W Q u := by
  ext j i
  by_cases e : j∈W i
  · rw [pane_read W Q u (h i) e]
    exact FreeResolvent.Pane.local_entry Q u ((↑) : W i → ι) Subtype.val_injective ⟨i,h i⟩ ⟨j,e⟩
  rw [pane_absent W Q u (Or.inr e)]
  exact FreeResolvent.Pane.unused Q u ((↑) : W i → ι) _ j (fun ⟨x,hx⟩ => e (hx ▸ x.property))

section Survey
variable {I : ι → Type} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
variable (T : FreeResolvent.Window.Survey I)









/-- Reindex a principal inverse. Include singular matrices; a caller
using the RHS as an inverse must still check positivity separately. -/
lemma inverse_reindex {α δ : Type*} [Fintype α] [Fintype δ] [DecidableEq α] [DecidableEq δ]
    (Q : Matrix α α ℝ) (e : δ ≃ α) :
    (Q.submatrix e e)⁻¹=(Q⁻¹).submatrix e e := by
  by_cases h : IsUnit Q.det
  · apply Matrix.inv_eq_right_inv
    rw [Matrix.submatrix_mul_equiv,Q.mul_nonsing_inv h]; ext i j
    simp [Matrix.one_apply]
  have ht : ¬IsUnit (Q.submatrix e e).det := by rwa [Matrix.det_submatrix_equiv_self]
  rw [Matrix.nonsing_inv_apply_not_isUnit _ h,Matrix.nonsing_inv_apply_not_isUnit _ ht, Matrix.submatrix_zero]
  rfl


end Survey

/-- The two halves of the covariance may read different principal matrices. -/
def mirror (D : Gaussian.Table ι) : Gaussian.Table ι := (1/2:ℝ) • (D + D.transpose)

lemma mirror_symm (D : Gaussian.Table ι) : (mirror D).IsSymm := by
  unfold mirror Matrix.IsSymm; simp [add_comm]





end YM.AnalyticBridge.LocalGaussianLaws
