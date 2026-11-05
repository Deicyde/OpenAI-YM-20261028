import YM.RemainderComparison.Flues.Trellis
import YM.Extra.MULTISOURCE_TRAJECTORIES.Packets

/-!
# Repack on duplicate forcing addresses: budget still per origin
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Flues
open Function Filter Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums Finset Merge Work.H03
open Mosaic Mosaic.Verse Marker GridRenewal.Rain Extra.Trajectories.Packets
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {ι θ : Type}[DecidableEq θ] {α:Type*} {J : Census θ}
variable (H:Yard ι α G n) (L:Scone ι α G n) (P:BudgetPoint) (root:ι→Support n)(Z:Set ι)
local notation "C" => fireplace H L
variable (F:ℕ ≃ (fireplace H L).Pellet) (a:α) (U:Config G n) (z:ι→Poly J)
variable {k:ℕ} {gV:θ→ℝ} (hZ:Serif.Chorus J gV Z z k) (h:H.Sounds P root) (hl:L.Rises P root)
local notation "D" => flash H L P Z F
local notation "M" => H.manifest a
variable {r v d b B σ w t y γ σ' : ℝ} {m : ℕ} (hp:H.Pays Z k m σ b)
variable (p:ℕ→ℕ) (A : Activities G n)(hr:∀ i,H.more i=A.forced (p i))
local notation "S" => H.song Z z a U
include hr
lemma admissible_dup (i:Finset ℕ): (M).admissible P U i↔ selected p (A.admissible P U) i:=by
   have he : i.biUnion (fun j=> (H.more j).inventory)= (i.image p).biUnion (fun j=> (A.forced j).inventory):=by ext x; simp [hr]
   constructor
   · intro hv
     have hz : (i:Set ℕ).InjOn p:=by
        intro x hx y hy hh; by_contra he
        have hm : Disjoint (H.more x).support (H.more y).support:= hv.1 hx hy he
        have ht : H.more y=H.more x := (hr y).trans ((congr_arg A.forced hh.symm).trans (hr x).symm)
        rw [ht] at hm; exact ((H.more x).inventory_ne.mono (H.more x).inventory_sup).ne_empty (disjoint_self.mp hm)
     refine ⟨⟨fun x hx y hy hd=>?_,he.symm.trans hv.2⟩,hz⟩; obtain ⟨x,hx',rfl⟩:= Finset.mem_image.mp (show x∈i.image p from hx); obtain ⟨y,hy',rfl⟩:=mem_image.mp (show y∈i.image p from hy); rw [←hr,←hr]; exact hv.1 hx' hy' (fun h=>hd (congr_arg p h))
   rintro ⟨⟨ha,hb⟩,hf⟩; refine ⟨fun x hx y hy hd=>?_,he.trans hb⟩; unfold Yard.manifest; dsimp only; rw [hr,hr]; exact ha (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) (fun h=>hd (hf hx hy h))
include hZ hp
lemma compact (V:ℕ→Poly J)(hV:∀ i,V i=∑' j:{j // p j=i},H.song Z z a U j.val)(hg:0≤ σ):
      HasSum (H.gala P Z z a U) (∑' i,Photo.fronts A V U P i):=by
   obtain ⟨hs,hv⟩:= yard_paid H P Z a U z hZ hp hg; unfold Merge.Photo.fronts; simp_rw [hV]
   have he : H.gala P Z z a U=value p (A.admissible P U) (S):=by
      ext1 i; unfold value Yard.gala Merge.Photo.fronts; rw [admissible_dup H P a U p A hr i]
   rw [he] at hv; rw [he,(repack p (A.admissible P U) (S) hv hs).tsum_eq]; exact hv.hasSum
-- joint consumer
omit hp hr
variable (hB:H.Pays Z k P.B (σ+1) b)(hP: L.Treasures Z k P.B (σ+1) v d) (hv: Resonant P.B k v b d σ B w t γ)
include hv hB hP hZ h hl
variable [Fintype θ]
lemma gale :
    Yard.Pays D Z k P.B σ B∧ Yard.Sounds D P root∧
    Summable (H.gala P Z z a U) ∧ Summable (L.plume Z z a U) ∧
    HasSum (Yard.gala D P Z z a U) ((∑' b,H.gala P Z z a U b)*cyclone (∑' i,L.plume Z z a U i)):=by
   have hp : 0 ≤ σ+1:= add_nonneg hv.exponent zero_le_one
   exact ⟨corner _ _ _ _ _ _ hv hB hP,flash_sound _ _ _ _ _ _ h hl,(yard_paid H P Z a U z hZ hB hp).2,(scone_budget L Z a U z hZ hP hp hv.small).1,gathering root Z F h hl _ (circles H L P Z a U z hZ hB hP hp hv.small)⟩
end YM.RemainderComparison.Flues
