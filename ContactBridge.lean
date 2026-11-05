import YM.Contacts.Solstice.Result
import YM.Contacts.Transport.Blend
import PublicWilson

/-! Restriction of the constructed full contact distribution to the collision-free locus. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open Function YM YM.Contacts YM.MultipleContact YM.Spec YM.Contacts.Normal YM.Contacts.Harvest
open YM.Contacts.Solstice YM.Contacts.Transport YM.OPE Filter MeasureTheory Set TopologicalSpace
open scoped Topology BigOperators Classical TensorProduct Distributions
variable {G : Gauge} {C : Family G} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (M : Devices F.sector.derivatives)
theorem contactDistribution (hM : MultipleLight F M) (s : Viewers F) (k : ℕ) (v : Fin k → S.Tag) :
    ∃ D : _root_.TestFunction (⊤ : Opens (Points k)) ℂ ⊤ →L[ℂ] ℂ,
    ∀ f : _root_.TestFunction (⊤ : Opens (Points k)) ℂ ⊤,
      tsupport f ⊆ WilsonFamily.separated k → D f = ∫ x, f x * S.useAt (spectator F s) x v := by
  let P := (LinearIsometryEquiv.refl ℝ (Points k)).toLinearIsometry
  let g : Normal.Group k := Finset.univ
  let d := fun j => (v j).1
  let t : Cells S d := fun j => (v j).2
  let B := min 1 (M.clearance (∑ i,d i+0))
  let r := B/4
  have hB : 0 < B := lt_min zero_lt_one (M.clearance_pos _)
  have hp : plane g ≤ LinearMap.range P.toLinearMap := fun x _ => ⟨x,rfl⟩
  have hc : Collapsed g (0 : Points k) := (collapsed_iff ..).mpr fun _ _ _ _ => rfl
  have R := hM.distribution (Points k) P g 0 hp hc d t s B r
    ⟨hB,min_le_left ..⟩ (min_le_right ..) ⟨by dsimp [r]; linarith, by dsimp [r]; linarith⟩
  refine ⟨R.record, fun f hf => ?_⟩
  rw [R.recorded]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  let u := unpack ⊤ f
  have hs : ∀ z ∈ tsupport u.val, P z + 0 ∈ conf k := by
    intro z hz
    rw [add_zero]
    exact hf hz
  have hh := harmonic M (0 : Points k) P r (root g) x u t (top_groups P _ hp hc) hs
  change readExpr M.basis (spectator F s) (localImage M P (root g) 0 r t u x) = _
  rw [hh, map_smul]
  change f x • readExpr M.basis (spectator F s) (fieldWord M.basis (P x+0).ofLp v) = _
  rw [read_fields M.basis M.coherent _ (spectate F s).laws.toSymmetric
    (spectate_respects F _) (spectate_ready F _), add_zero]
  change f x • (if x ∈ conf k then S.useAt (spectator F s) x v else 0) = _
  split
  · rfl
  next hx =>
    have hz : f x = 0 := notMem_support.mp fun h => hx (hf (subset_closure h))
    simp [hz]
end YangMills
