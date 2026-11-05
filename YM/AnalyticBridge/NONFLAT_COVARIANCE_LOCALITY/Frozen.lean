import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Panels
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Completion

/-!
# The unintegrated counting slots

Complete by identity on all frozen/tree slots. Needed e.g. for absolute
local tests at any address independent of which of its chosen partners ended
up being active. No harmonic (or even harmonic-like) coordinates deleted.
Prove this reads the same C under the positive prerequisites. Also compare
on a local patch of A even when remote output flags were wrong, for
later localization (we are not asserting full-space identities then).
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality.Full
open Function Filter Lattice RG Wilson Pressure Tree Matrix
open Next.SectorChange Next.SectorChange.Schur Next.SectorChange.Completion
open FreeResolvent Mark TestD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

-- Principal windows reindex equivariantly; no det hypothesis.
lemma reflect_windows {p : α → Set α} {q : β → Set β} (e : α ≃ β)
    (he : ∀ i : α, p i=e ⁻¹' (q (e i))) (hx : ∀ i, i∈p i)
    (M : Matrix β β ℝ) (u : ℝ) :
    (panes q u M).submatrix e e=panes p u (M.submatrix e e) := by
  ext j i
  by_cases h : j∈p i
  · have hv : e i∈q (e i) := Set.mem_preimage.mp (he i ▸ hx i)
    have hw : e j∈q (e i) := Set.mem_preimage.mp (he i ▸ h)
    let a : p i ≃ q (e i) := Equiv.subtypeEquiv e (fun x => by rw [he]; rfl)
    have ht : ((Schur.principal M (q (e i))+u • 1).submatrix a a)=
        Schur.principal (M.submatrix e e) (p i) + u • 1 := by
      rw [shift_compress _ _ _ a.injective]; rfl
    change panes q u M (e j) (e i)=_
    rw [read_panes q u M _ _ hv hw, read_panes p u _ _ _ (hx i) h,← ht, Matrix.inv_submatrix_equiv]
    rfl
  have hj : e j ∉ q (e i) := fun hb => h ((he i).symm ▸ Set.mem_preimage.mpr hb)
  change panes q u M (e j) (e i)=_
  exact (hidden_pane _ _ _ hj).trans (hidden_pane _ _ _ h).symm

private def waiters (W : Set (α⊕β)) := Sum.inl ⁻¹' W
private def blanks (W : Set (α⊕β)) := Sum.inr ⁻¹' W
private def cutMap (W : Set (α⊕β)) : ((waiters W : Type) ⊕ (blanks W : Type)) ≃ W where
  toFun := Sum.elim (fun ⟨i,hi⟩ => ⟨Sum.inl i,hi⟩) (fun ⟨i,hi⟩ => ⟨Sum.inr i,hi⟩)
  invFun
    | ⟨.inl i,hi⟩ => .inl ⟨i,hi⟩
    | ⟨.inr i,hi⟩ => .inr ⟨i,hi⟩
  left_inv := by rintro (i|i) <;> rfl
  right_inv := by rintro ⟨i|i,hi⟩ <;> rfl

omit [Fintype α] [Fintype β] in
private lemma shifts (A : Matrix α α ℝ) (s : Set (α⊕β)) (u : ℝ) :
    let B := Schur.principal (wide A 1) s + u • 1
    B.submatrix (cutMap s) (cutMap s) = wide (Schur.principal A (waiters s) + u • 1)
      ((1:Gaussian.Table (blanks s))+u • 1) := by
  intro B; unfold B
  rw [shift_compress _ _ _ (cutMap s).injective]
  have ht : (Schur.principal (wide A 1) s).submatrix (cutMap s) (cutMap s) =
      wide (Schur.principal A (waiters s)) (1:Gaussian.Table (blanks s)) := by
    ext (i|i) (j|j) <;> first | rfl | skip
    change (1:Gaussian.Table β) i.val j.val=(1:Gaussian.Table (blanks s)) i j
    simp [Matrix.one_apply, Subtype.val_inj]
  rw [ht]
  ext (i|i) (j|j) <;> simp [wide,Matrix.one_apply]

private lemma gap_blank (u : ℝ) : FreeResolvent.Gap ((1:Gaussian.Table β)+u • 1) (1+u) :=
  (show FreeResolvent.Gap (1:Gaussian.Table β) 1 from ⟨fun v => by simp⟩).shift u






/-- Even when other panels might be singular (in a localization proof)
the *side* reading on the active columns can use the full convention. No
positivity from this identity; on a singular active window both sides read
Lean's total (junk) inverse. Need explicit external receipt to establish
invertibility or to use the Gaussian. -/
lemma side (W : α⊕β → Set (α⊕β)) {s : α → Set α} (A : Matrix α α ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hW : ∀ i : α, Sum.inl i∈W (.inl i)) (hs : s = fun i => Sum.inl ⁻¹' W (.inl i)) (i j : α) :
    panes W u (wide A 1) (.inl j) (.inl i) = panes s u A j i := by
  subst hs
  let X i := waiters (W (.inl i))
  change _ = panes X u A j i
  by_cases h : Sum.inl j∈W (.inl i)
  · let s := W (.inl i)
    let M := Schur.principal (wide A (1:Gaussian.Table β)) s + u • 1
    let T := cutMap s
    let N := Schur.principal A (waiters s) + u • 1
    have ht : M.submatrix T T = _ := shifts A s u
    let q : waiters s := ⟨i,hW i⟩
    let v : waiters s := ⟨j,h⟩
    rw [read_panes W u _ _ _ (hW i) h,read_panes X u _ i j (hW i) h]
    change (M⁻¹.submatrix T T) (.inl v) (.inl q)=N⁻¹ v q
    rw [← Matrix.inv_submatrix_equiv,ht]
    let D := (1:Gaussian.Table (blanks s))+u • 1
    change (wide N D)⁻¹ _ _ = N⁻¹ _ _
    by_cases h : IsUnit N.det
    · rw [wide_inv N D h ((gap_blank u).unit_det (by linarith))]; rfl
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ ?_]; rfl
    rw [wide_det N D]; exact fun hh => h (isUnit_of_mul_isUnit_left hh)
  exact (hidden_pane W _ _ h).trans (hidden_pane X u A h).symm


-- Off-block is zero even when numerical positivity in this evaluation
-- not bought. Useful with `side` for vectors computed on the table.
lemma across (W : α⊕β → Set (α⊕β)) (A : Matrix α α ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hW : ∀ i : α⊕β, i∈W i) (i : α) (j : β) :
    panes W u (wide A 1) (.inl i) (.inr j) = 0 ∧ panes W u (wide A 1) (.inr j) (.inl i) = 0 := by
  let Z := wide A (1:Gaussian.Table β)
  let X s := Schur.principal Z s + u • 1
  have hh (s : Set (α⊕β)) (i : waiters s) (j : blanks s) :
      ((X s)⁻¹.submatrix (cutMap s) (cutMap s)) (.inl i) (.inr j)=0 ∧
      ((X s)⁻¹.submatrix (cutMap s) (cutMap s)) (.inr j) (.inl i)=0 := by
    rw [← Matrix.inv_submatrix_equiv]
    have ht : (X s).submatrix (cutMap s) (cutMap s)=_ := shifts A s u
    rw [ht]; let N := Schur.principal A (waiters s) + u • 1
    let M := (1:Gaussian.Table (blanks s))+u • 1
    by_cases H : IsUnit N.det
    · rw [wide_inv N M H ((gap_blank u).unit_det (by linarith))]; exact ⟨rfl,rfl⟩
    rw [Matrix.nonsing_inv_apply_not_isUnit _ ?_]; exact ⟨rfl,rfl⟩
    rw [wide_det]; exact fun h=> H (isUnit_of_mul_isUnit_left h)
  constructor
  · by_cases hx : Sum.inl i∈W (.inr j)
    · rw [read_panes W u _ _ _ (hW _) hx]
      exact (hh _ ⟨i,hx⟩ ⟨j,hW (.inr j)⟩).1
    exact hidden_pane W u _ hx
  by_cases hx : Sum.inr j∈W (.inl i)
  · rw [read_panes W u _ _ _ (hW _) hx]; exact (hh _ ⟨i,hW (.inl i)⟩ ⟨j,hx⟩).2
  exact hidden_pane W u _ hx

end YM.AnalyticBridge.NonflatCovarianceLocality.Full
