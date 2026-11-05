import YM.Push.SECTOR_MEASURE.Cells
import YM.Work.B04
import YM.Work.E01
import YM.Work.F01
-- E01/E08 usable estimates are already imported by Fluctuations



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Truly inactive vs still integrated (one oriented step)

The `Stores.limit`, etc. already charge rows in the assigned region; they are gone in
`unassigned`. Use strictly exterior anchors (assignment includes the boundary). Their whole
short scale needs can be met on the actual intact Allocation. Use projections of *initial*
endpoints throughout (a larger list of frozen links, e.g. using both projections, is also
fine but check the buffer at every use). No independent tags or roll of the trees in the
link estimates. Does not apply to dropping defaults: requires Seeded (or establish these
conclusions again on the needed halos).
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder

open Filter Function Lattice RG Wilson Pressure Pressure.Stores Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S}

/-- Initial root beyond 4B. Only ask to integrate these non-tree bonds with small scale costs.
All projection/ownership counted again in native units. -/
def remote (A : Stores S) (B : ℕ) (b : Bond f) : Prop := S.ratio.parent b.1 ∉ A.dome (4*B)

def regular (A : Stores S) (B : ℕ) (F : Forest S.ratio) :=
  (Finset.univ : Finset F.Free).filter fun i => remote A B (i:F.Free).val

def frozen (A : Stores S) (B : ℕ) (F : Forest S.ratio) := (regular A B F)ᶜ

lemma outside_dome {R r : ℕ} {x y : Site c} (h : x ∉ A.dome R)
    (e : separation x y + r ≤ R) : y ∉ A.dome r := by
  intro hh; obtain ⟨i,hi,ha⟩ := halo_spec.mp hh
  apply h (halo_spec.mpr ⟨i,hi,?_⟩)
  apply (separation_triangle i y x).trans; rw [separation_comm y x]; omega

variable {V : Config G c} {U : Config G f} {k : S.Choices} {x W : ℝ}

/-- Default V plaquette at any near query in the seed-free exterior, even without hard
booking; all allocations support this. -/
lemma exterior_output (h : Seeded A U k V x W) {b : Cell c} (he : b.1 ∉ A.place) :
    toll V b ≤ temp x := by
  by_contra! hv
  apply he; unfold Stores.place
  apply Finset.mem_union.mpr (Or.inr ?_)
  rw [h.exactFlags]; exact (RG.flags_spec ..).mpr ⟨b,Work.E01.base_touched _,hv⟩

lemma exterior_fine (h : Seeded A U k V x W) {b : Cell f} (he : S.ratio.parent b.1 ∉ A.place) :
    toll U b ≤ fiery G x S.patch.L/2 := by
  refine (h.fine b).2 (fun hi => he (Finset.mem_union_left _ <| Finset.mem_union_left _ ?_))
  exact Finset.mem_biUnion.mpr ⟨b,hi,Finset.mem_image_of_mem _ (Work.E01.base_touched _)⟩

lemma exterior_noise (h : Seeded A U k V x W) {b : Bond c} (he : b.1 ∉ A.place) :
    wire (S.prediction U k) V b ≤ 2*W*fiery G x S.patch.L := by
  refine (h.coarse b).2 (fun hi => he (Finset.mem_union_left _ <| Finset.mem_union_right _ ?_))
  exact Finset.mem_biUnion.mpr ⟨b,hi,by simp [pinPos]⟩

lemma default_fine (h : Seeded A U k V x W) {b : Cell f} (he : b ∉ A.limit x) :
    toll U b ≤ fiery G x S.patch.L := by
  have hu : S.ratio.parent b.1 ∉ A.dome (2*radiusB x) :=
    fun hh => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
  apply (exterior_fine h (fun hp => hu (halo_subset _ _ hp))).trans
  have hh : 0 ≤ fiery G x S.patch.L := temp_nonneg _
  linarith

lemma default_output (h : Seeded A U k V x W) {b : Cell c} (he : b ∉ A.outs x) :
    toll V b ≤ temp x := exterior_output h (fun hp => he
      (Finset.mem_filter.mpr ⟨Finset.mem_univ b,halo_subset _ _ hp⟩))

lemma default_keeps (h : Seeded A U k V x W) (T : Tube G S) (D : ℝ)
    (hm : Bid.LaneCounts T.up x (fiery G x S.patch.L) T.high D 1 S.ratio.parent)
    {b : Cell f} (he : b ∉ A.limit x) : PathData.kept T.high (fiery G x S.patch.L) b.1 U := by
  have hx : S.ratio.parent b.1 ∉ A.dome (2*radiusB x) :=
    fun hh => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
  intro p; by_contra! hv
  have hr := hm.dropped _ _ p hv
  have hp : S.ratio.parent p.1 ∉ A.place := fun hh =>
    hx (halo_spec.mpr ⟨_,hh,(separation_comm ..) ▸ (show separation (S.ratio.parent b.1) (S.ratio.parent p.1) ≤ 2*radiusB x by omega)⟩)
  have ht := exterior_fine h (b:=p) hp
  have hs := T.high.radius_pos
  have hi := lt_of_le_of_lt (le_mul_of_one_le_right
    (show 0≤fiery G x S.patch.L from temp_nonneg _) (Real.one_le_exp (show
      0≤(separation b.1 p.1:ℝ)/T.high.relaxation by positivity))) hv
  have hT : 0 ≤ fiery G x S.patch.L := temp_nonneg _
  change fiery _ _ _ < toll U p at hi
  linarith

lemma uses_all (h : Alive S U k) (i : Site c) : usable S U i k := fun _ _ => listed_of_alive h _

lemma sum_free_le (F : Forest S.ratio) (g : Bond f → ℝ) (h : ∀ b, 0 ≤ g b) :
    (∑ i : F.Free, g i) ≤ ∑ b, g b := by
  classical
  let e := (fun i : F.Free => (i : Bond f))
  have he : Injective e := Subtype.val_injective
  calc
    _ = ∑ i ∈ Finset.univ.image e, g i := by rw [Finset.sum_image (by intro i _ j _ hh; exact he hh)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => h i

lemma frozen_card (A : Stores S) (B : ℕ) (F : Forest S.ratio) :
    (frozen A B F).card ≤ S.patch.L.val^4 * Fintype.card Axis * 4 * (8*B+1)^4 * A.shares := by
  let g := S.ratio
  let H (b : Bond c) := if b.1 ∈ A.dome (4*B) then (1:ℝ) else 0
  have he : ∑ b, H b = (Fintype.card Axis:ℝ)*(A.dome (4*B)).card := by
    rw [Fintype.sum_prod_type]
    unfold H; change (∑ i : Site c, ∑ _j : Axis, if i ∈ A.dome (4*B) then (1:ℝ) else 0) = _
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [show (∑ i : Site c, (Fintype.card Axis:ℝ)*if i ∈ A.dome (4*B) then 1 else 0) = _ from
      (Finset.mul_sum ..).symm]; simp [← Finset.sum_filter]
  have ha := sum_free_le F (fun i => H (g.parent i.1,i.2)) (by intros; unfold H; split <;> norm_num)
  change (∑ i : F.Free, H (g.parent i.val.1,i.val.2)) ≤ _ at ha
  rw [Work.F01.sum_parent_bond g H,he,site_card] at ha
  have eq : frozen A B F = Finset.univ.filter (fun i : F.Free => g.parent i.val.1 ∈ A.dome (4*B)) := by
    ext i; simp [frozen,regular,remote,g]
  unfold H at ha
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one, ← eq] at ha
  have hh : (A.dome (4*B)).card ≤ 4*A.shares*(8*B+1)^4 := by
    apply (Corona.halo_size A.place (4*B)).trans
    rw [show 4*B+4*B=8*B by ring]; exact Nat.mul_le_mul_right _ (Work.E01.place_card _)
  have ht : (frozen A B F).card ≤ S.patch.L.val^4 * (Fintype.card Axis * (A.dome (4*B)).card) := by
    exact_mod_cast ha
  exact ht.trans ((Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hh)).trans_eq (by ring))



end YM.SectorNext.Remainder
