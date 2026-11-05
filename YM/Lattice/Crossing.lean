import YM.Lattice.Foliation
import YM.Lattice.Scale

/-!
# One step in the centered block geometry

Keep working with our lifted tie convention. `parents_hop` also if
coarse dimension=1. When computing `copied`, the sector consumer may
assume `c>1` and so no ambiguity between internal and crossing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Lattice.Ratio

open Finset Function
open scoped BigOperators
variable {c f : Side} (g : Ratio c f)

lemma half_box (h : Odd g.count.val) : ∀ x : Site g.count, lift x ∈ box (g.count.val/2) := by
  intro x
  rw [box_iff_layers]; intro i
  have hl := lift_centers x i
  unfold layers; rw [mem_Icc]
  obtain ⟨j,hj⟩ := h
  omega

lemma half_lift (h : Odd g.count.val) (x : Cover) (hx : x∈box (g.count.val/2)) : lift (wrap g.count x)=x := by
  apply lift_eq_iff.mpr ⟨rfl,?_⟩
  intro i
  have he := (box_iff_layers ..).mp hx i
  unfold layers at he; rw [mem_Icc] at he; obtain ⟨j,hj⟩ := h; omega

lemma embed_parent (x : Site c) : g.parent (g.embed x)=x := by
  have he : lift (0 : Site g.count)=0 := by funext; simp [lift]
  have h : g.assemble (x,0)=g.embed x := by simp [assemble, he]
  rw [← h]; exact g.assemble_parent (x,0)

lemma embed_leap (x : Site c) (i : Axis) : g.embed (x+step i)=g.embed x+g.count.val • step i := by
  have he : g.embed (step i)=_ := calc
    g.embed (step i)=g.embed (wrap _ (step i)) := by rw [wrap_step]
    _ = _ := g.embed_wrap (step i)
  rw [show g.embed (x+step i)=_ from g.root.map_add x (step i), root_embed,root_embed,he,map_nsmul,wrap_step]

lemma root_id (x : Site f) : x=g.embed (g.parent x) ↔ g.residue x=0 := by
  constructor
  · intro h; rw [h,g.residue_embed]
  intro h
  have he : lift (0:Site g.count)=0 := by funext; simp [lift]
  have H := g.unpack_at x
  rw [h,he,map_zero,add_zero] at H
  exact H.symm

/-- Determine parent of the neighbor to apply T_cp. -/
theorem parents_hop (h : Odd g.count.val) (x : Site f) (i : Axis) :
    g.parent (x+step i)=if lift (g.residue x) i=(g.count.val/2 : ℕ) then g.parent x+step i else g.parent x := by
  let q := lift (g.residue x)
  let R := g.count.val/2
  have ht : g.embed (g.parent x)+wrap f q = x := g.unpack_at x
  have hx := (box_iff_layers ..).mp (g.half_box h (g.residue x))
  have hp (b : Site c) (u : Cover) (hu : u∈box R) : g.parent (g.embed b+wrap f u)=b := by
    rw [show g.embed b+wrap f u=g.assemble (b,wrap g.count u) by rw [assemble, g.half_lift h u hu]]
    exact g.assemble_parent _
  split_ifs with he
  · let u := q+step i-g.count.val • step i
    have hi : u∈box R := by
      rw [box_iff_layers]; intro j
      have hj := hx j
      obtain ⟨k,hK⟩ := h
      by_cases H : j=i
      · subst j
        unfold u; rw [layers,mem_Icc]; simp only [Pi.sub_apply,Pi.add_apply ,Pi.smul_apply]
        simp only [nsmul_eq_mul,
          step_apply,↓reduceIte,mul_one,q,he]; unfold R; omega
      simpa [u,H] using hj
    rw [show x+step i=g.embed (g.parent x+step i)+ wrap f u by
      rw [← ht,ht,g.embed_leap]; unfold u
      rw [map_sub,map_add,map_nsmul,wrap_step]; rw [show _+ _+( (_+_) - _)=(g.embed (g.parent x)+wrap f q)+step i by abel,ht]]
    exact hp _ _ hi
  have hb : q+step i∈box R := by
    rw [box_iff_layers]; intro j; have hj := hx j
    by_cases H : j=i
    · subst j; unfold layers R q at *; rw [mem_Icc] at hj ⊢; simp only [Pi.add_apply,step_apply, ↓reduceIte]; omega
    simpa [H] using hj
  rw [show x+step i=g.embed (g.parent x)+wrap f (q+step i) by rw [map_add,wrap_step, ← add_assoc,ht]]; exact hp _ _ hb

lemma internal (h : Odd g.count.val) {x : Site f} {i : Step}
    (hx : lift (g.residue x)+i.vec∈box (g.count.val/2)) :
    lift (g.residue (x+i.vec))=lift (g.residue x)+i.vec ∧ g.parent (x+i.vec)=g.parent x := by
  let H := lift (g.residue x)+i.vec
  have ha : x+i.vec=g.assemble (g.parent x,wrap g.count H) := by
    rw [assemble,g.half_lift h _ hx]; dsimp only; rw [map_add,wrap_vec,← add_assoc,g.unpack_at]
  conv => congr
          · lhs; rw [ha]
          · lhs; rw [ha]
  rw [assemble_res, half_lift _ h _ hx, assemble_parent]; simp
end YM.Lattice.Ratio
