import YM.Extra.SOURCE_HISTORIES.Motion
import YM.Work.H03

/-! Change anchor by genuine lattice TRANSLATION on fitted hierarchy steps.
Price at current masks, and reimburse identical mass. Not a rotational norm
assertion (signed, which can change weighted derivative prices, distinct).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Drift
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
variable (t : Site n)

def relocated (Y : Support n) := Y.image (·+t)

lemma aff : affine 1 t = (·+t) := funext fun x => by simp [affine]
lemma through (Y : Support n) (x) : x∈Y ↔ x+t∈relocated t Y := by
  simp [relocated]

lemma halo_drift (Y : Support n) (M : ℕ) : relocated t (halo M Y) = halo M (relocated t Y) := by
  ext x
  obtain ⟨z,rfl⟩ := (Equiv.addRight t).surjective x
  change z+t ∈ _ ↔ z+t ∈ _
  rw [← through,halo_spec,halo_spec]
  constructor
  · rintro ⟨i,h,hx⟩
    exact ⟨_,(through t Y i).1 h,by simpa only [separation_translate] using hx⟩
  rintro ⟨i,h,hx⟩
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
  exact ⟨i,hi,by simpa only [separation_translate] using hx⟩

private lemma area_le (Y : Support n) (M : ℕ) : coverNumber M (relocated t Y) ≤ coverNumber M Y := by
  obtain ⟨c,hc,h⟩ := coverNumber_realized M Y
  refine le_trans (Corona.list_cost M (D:=relocated t c) ⟨?_,?_⟩) ?_
  · rw [← halo_drift]; exact Finset.image_subset_image hc.1
  · rw [← halo_drift]
    intro x hx y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    refine Relation.ReflTransGen.lift (·+t) ?_ _ _ (hc.2 _ hi _ hj)
    intro a b h
    exact ⟨(through ..).1 h.1,(through ..).1 h.2.1,separation_translate .. |>.trans_le h.2.2⟩
  exact Finset.card_image_le.trans_eq h

lemma area (Y : Support n) (M : ℕ) : coverNumber M (relocated t Y)=coverNumber M Y := by
  refine le_antisymm (area_le t Y M) ?_
  simpa only [relocated,Finset.image_image,comp_def, add_neg_cancel_right,Finset.image_id'] using area_le (-t) (relocated t Y) M

lemma flag (U : Config G n) (a) : relocated t (flags a (translate t U)) = flags a U := by
  have he := Work.H03.flags_send 1 t a U
  rw [aff,pull_one] at he; exact he















/-- Left derivative translation no inversion of links. -/
def directions : Directions G n →ₗ[ℝ] Directions G n where
  toFun v i := v (i.1+t,i.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl













end YM.Extra.Histories.Drift
