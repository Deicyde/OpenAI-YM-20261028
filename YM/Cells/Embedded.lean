import YM.Cells.Certificate

/-!
# Insert at some cells and estimate (not all centered at own base proofs)
Uses original transforms on distinct addresses and gauge invariant measurability.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells.Tiling
open MeasureTheory Measure Filter Function Set Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {G : Gauge} (T : Tiling n) {ι : Type*} [Fintype ι]

@[simp] lemma copy_one (i : T.Cell) : T.copy i (G := G) 1=1 := by
  funext x; unfold copy; split <;> simp

@[simp] lemma root_one (β : ℝ) : T.rootTest (G := G) β 1=1 := by simp [rootTest,moment]

lemma receiving {α : Type*} [CommMonoid α] (f : T.Cell → α) (c : ι → T.Cell) (h : Injective c)
    (hw : ∀ i, (∀ j, c j ≠ i) → f i=1) : ∏ i : T.Cell, f i = ∏ i : ι, f (c i) := by
  classical
  rw [← Finset.prod_image (s := Finset.univ) (f := f) (show _ from h.injOn)]
  symm; exact Finset.prod_subset (Finset.subset_univ _) fun x _ hx => hw x (by simpa using hx)

theorem planted {β} (H : Seam G n β) (c : ι → T.Cell) (hc : Injective c)
    (v : ι → Config G n → ℂ) (hx : ∀ i, Interior (T.chamber 0) (v i)) :
    ‖moment β (fun U => ∏ i, T.copy (c i) (v i) U)‖ ≤ ∏ i, T.rootTest β (v i) := by
  classical
  let F : T.Cell → Config G n → ℂ := fun x => if h : ∃ i, c i=x then v (Classical.choose h) else 1
  have he i : F (c i)=v i := by unfold F; rw [dif_pos ⟨i,rfl⟩]; exact congr_arg v (hc (Classical.choose_spec (show ∃ j,c j=c i from ⟨i,rfl⟩)))
  have hp i (h : ∀ j, c j≠i) : F i=1 := by simp [F,h]
  have ht := H.inequality T F fun i => show Interior (T.chamber 0) (F i) from by unfold F;split; exact hx _; exact Interior.constant _ _
  have hᵣ (U) : ∏ i, T.copy i (F i) U=∏ j : ι, T.copy (c j) (v j) U := by
    rw [T.receiving _ c hc (fun i hh => ?_)]
    · simp_rw [he]
    rw [hp i hh,T.copy_one]; rfl
  simp_rw [hᵣ,T.receiving _ c hc (fun i hi => show T.rootTest β (F i)=1 by rw [hp i hi,T.root_one]),he] at ht
  exact ht
end YM.Cells.Tiling
