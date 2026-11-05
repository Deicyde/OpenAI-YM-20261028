import YM.Push.LOCAL_SPLITTING.Raw


/-! Moving a chosen reservation coherently in the same vacuum; detailed
commutation of Raw.build (including both kinds of produced remainder) for
transported slots. If regular-address names are also permuted, one can carry
those along separately. Even for independent slot choices primary moves need
no assumption on equality of reservations (`Raw.build_pull`). Neither statement
asserts same-index forced values at different placements without moving/regrouping
labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {s : Signed} {b : Site n}

namespace Slots
variable {ι : Type*} {A : Activities G n} {X Y : ι → Support n} (m : A.Moves s b)
    (h : ∀ i, Y i = (X i).image (affine s b))
include h
private theorem packs_turn (q : Finset ℕ) (i : ι) : Packs A (X i) q ↔ Packs A (Y i) (m.kp.finsetCongr q) := by
  change Packs A (X i) q ↔ Packs A (Y i) (q.map _)
  have hd (j k) : Disjoint (patch A (m.kp j)) (patch A (m.kp k)) ↔ Disjoint (patch A j) (patch A k) := by rw [patch,patch,m.forced_support,m.forced_support]; exact Finset.disjoint_image (turnSites s b).injective
  have he (j) : Disjoint (Y i) (patch A (m.kp j)) ↔ Disjoint (X i) (patch A j) := by rw [patch,m.forced_support,h]; exact Finset.disjoint_image (turnSites s b).injective
  constructor
  · intro hx; refine ⟨hx.nonempty.map,fun j hj k hk hN => ?_,fun j hj => ?_⟩
    · obtain ⟨j,H,rfl⟩ := Finset.mem_map.mp hj; obtain ⟨k,H',rfl⟩ := Finset.mem_map.mp hk
      exact (hd ..).2 (hx.separate H H' (fun he => hN (he ▸ rfl)))
    obtain ⟨j,H,rfl⟩ := Finset.mem_map.mp hj; exact mt (he j).mp (hx.hits _ H)
  intro hx; refine ⟨Finset.map_nonempty.mp hx.nonempty,fun j hj k hk hN => (hd j k).1 (hx.separate (Finset.mem_map_of_mem _ hj) (Finset.mem_map_of_mem _ hk) (m.kp.injective.ne hN)), fun j hj => mt (he j).mpr (hx.hits _ (Finset.mem_map_of_mem _ hj))⟩

def relocate : Letters A X ≃ Letters A Y := Equiv.sigmaCongrRight fun i => m.kp.finsetCongr.subtypeEquiv fun q => packs_turn m h q i

omit h in
private theorem map_data (p : ℕ → Support n) (hp : ∀ i,p (m.kp i)=(p i).image (affine s b)) (q : Finset ℕ) :
    (q.map m.kp.toEmbedding).biUnion p = (q.biUnion p).image (affine s b) := by
  ext x; simp only [Finset.mem_biUnion,Finset.mem_map, Finset.mem_image,Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨j,⟨k,hk,rfl⟩,hx⟩; rw [hp] at hx; obtain ⟨x,H,rfl⟩ := Finset.mem_image.mp hx; exact ⟨_,⟨k,hk,H⟩,rfl⟩
  rintro ⟨x,⟨k,hk,hx⟩,rfl⟩; exact ⟨_,⟨k,hk,rfl⟩,hp k ▸ Finset.mem_image_of_mem _ hx⟩

def move (S : Slots A X) : Slots A Y where
  label := (relocate m h).symm.toEmbedding.trans (S.label.trans m.kp.toEmbedding)
  support u := by
    obtain ⟨u,rfl⟩ := (relocate m h).surjective u
    change patch A (m.kp (S.label ((relocate m h).symm _))) = Y u.1 ∪ (u.bundle.map m.kp.toEmbedding).biUnion _
    rw [Equiv.symm_apply_apply,patch,m.forced_support, ← patch, S.support,Letters.total,Finset.image_union, h,map_data m _ m.forced_support]
  inventory u := by
    obtain ⟨u,rfl⟩ := (relocate m h).surjective u
    change flagsFor A (m.kp (S.label ((relocate m h).symm _))) = (u.bundle.map m.kp.toEmbedding).biUnion _
    rw [Equiv.symm_apply_apply,flagsFor,m.forced_inventory,← flagsFor, S.inventory,map_data m _ m.forced_inventory]; rfl
  allows u U := (m.forced_tests ..).mpr (S.allows ..)


end Slots

namespace Raw
variable {d : ℕ} {F : Labels.Frame G d} {R : Rep G n} (m : R.activities.Moves s b) (M : Raw F n)
def move : Raw F n where
  seed := F.act s.ortho M.seed
  bulk i := M.bulk i ∘ pull s b
  forced i := M.forced (m.kp.symm i) ∘ pull s b

variable {X : ℕ → Support n} {A : Hol G} {T : SectionData F} {o : Site n}








end Raw
end YM.Push.Local
