import YM.Slice.Mirror

/-! Classification of leaf and bond layers for the two seam types. Supports not
on axes `a ≠ C.pos` propagate in the same slice. Care for seam adjacency, turns and strictness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open Function Set MeasureTheory
open Lattice Wilson Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n : Side} (C : Cut n)

/- Open positive sector for leaf variables. -/
def res (v : Per n) : ℕ := (v-C.baseLine).val

def Plus (v) := C.kind.Strict C.half.val (res C v)
-- Minus is reflected Plus. For threads use shifted level index:
def imageChord (v : Per n) := level C v - 1

def bridge (v : Per n) := res C v + C.kind.shift < C.half.val

@[simp] theorem chord_end (v) : level C (v+1) = imageChord C v := by unfold level imageChord level; ring
@[simp] theorem chord_turn (v) : imageChord C (imageChord C v) = v := by unfold imageChord level; ring

private lemma toRealSide (v : Per n) : C.baseLine + (res C v : Per n) = v := by simp [res,Per]
private lemma shorter (v) : res C v<n.val := ZMod.val_lt _
private lemma trivialRes (v : ℕ) (h : v<n.val) : res C (C.baseLine + (v : Per n)) = v := by
  simp [res,Per,h,Nat.mod_eq_of_lt]

private lemma ofLevel (v y) (i) (h : i < n.val)
    (H : v - C.baseLine = (i : Per n)) (hV : v=y) : res C y = i := by
  subst y
  rw [res,H,ZMod.val_natCast_of_lt h]

variable {C}
private lemma three (j : ℕ) (hj : j ≤ n.val) :
    (((n.val-j : ℕ):ℕ) : Per n) = -(j:Per n) := by rw [Nat.cast_sub hj]; simp [Per]

variable (C) in
private lemma line_relation (x : Per n) : (res C x : Per n) = x-C.baseLine := by simp [res,Per]

lemma opposite_line_link (h : C.kind=.link) (x : Per n) : res C (level C x) = n.val - (res C x+1) := by
  have hk := shorter C x
  apply ofLevel C (level C x) _ _ (by omega) _ rfl
  rw [three _ hk]
  unfold level; rw [h]
  push_cast
  simp [Kind.shift,line_relation]; ring

lemma opposite_line_site (h : C.kind=.site) {x : Per n} (hx : 0 < res C x) : res C (level C x) = n.val - res C x := by
  have hk := shorter C x
  apply ofLevel C (level C x) _ _ (by omega) _ rfl
  unfold level; rw [three _ hk.le,h,line_relation]; simp [Kind.shift]; ring

lemma opposite_wire_site (h : C.kind=.site) (x : Per n) : res C (imageChord C x) = n.val - (res C x+1) := by
  have hk := shorter C x
  apply ofLevel C (imageChord C x) _ _ (by omega) _ rfl
  rw [three _ hk]
  unfold imageChord level; rw [h]
  push_cast
  simp [Kind.shift,line_relation]; ring

lemma opposite_wire_link (h : C.kind=.link) {x : Per n} (hw : res C x+1 < n.val) :
    res C (imageChord C x) = n.val - (res C x+1+1) := by
  apply ofLevel C (imageChord C x) _ _ (by omega) _ rfl
  rw [three _ hw]
  unfold imageChord level; rw [h]
  push_cast
  simp [Kind.shift,line_relation]; ring

/-- Indices read on hyperplanes themselves (site cuts) or always empty (link). -/
def pier (C : Cut n) : Set (Per n) := {x | ¬ Plus C x ∧ ¬ Plus C (level C x)}

def gate (C : Cut n) : Set (Per n) := {x | ¬ bridge C x ∧ ¬ bridge C (imageChord C x)}

lemma opposite_leaf {x : Per n} (hx : Plus C x) : ¬ Plus C (level C x) := by
  unfold Plus at *
  have h := C.even
  rcases H:C.kind with _|_
  · rw [H] at hx; have ht : res C x<C.half.val := hx.2
    rw [opposite_line_site H hx.1]; change ¬ (0 < n.val-res C x ∧ _); unfold Kind.Strict at *; omega
  rw [H] at hx
  rw [opposite_line_link H]; unfold Kind.Strict at *; omega

lemma opposite_time {x : Per n} (hx : bridge C x) : ¬ bridge C (imageChord C x) := by
  unfold bridge at *
  have h := C.even
  cases H:C.kind with
  | site => rw [opposite_wire_site H]; rw [H] at hx; simp only [Kind.shift] at hx ⊢; omega
  | link =>
    rw [H] at hx; simp only [Kind.shift] at hx
    rw [opposite_wire_link H (by omega)]; simp only [Kind.shift] at ⊢; omega

lemma walls_link (h : C.kind=.link) : IsEmpty ↥(pier C) := ⟨fun x => by
  obtain ⟨x,hx⟩ := x
  change ¬Plus C _ ∧ ¬Plus C _ at hx
  unfold Plus at hx; rw [h,opposite_line_link h] at hx
  unfold Kind.Strict at hx
  have := C.even; have he : 0<C.half.val := C.half.property; omega⟩

lemma gates_site (h : C.kind=.site) : IsEmpty ↥(gate C) := ⟨fun x => by
  obtain ⟨x,hx⟩ := x
  change ¬bridge C _ ∧ ¬bridge C _ at hx
  unfold bridge at hx; rw [h,opposite_wire_site h] at hx
  simp only [Kind.shift] at hx
  have := C.even; have he : 0<C.half.val := C.half.property; omega⟩

lemma fixed_pier {x : Per n} (hx : x ∈ pier C) : level C x=x := by
  cases h : C.kind with
  | link => exact (walls_link h).false (⟨x,hx⟩ : pier C) |>.elim
  | site =>
    change ¬Plus C _ ∧ ¬Plus C _ at hx
    unfold Plus at hx
    rw [h] at hx
    unfold Kind.Strict at hx
    cases Nat.eq_zero_or_pos (res C x) with
    | inl e => rw [← toRealSide C x,e,level,h]; simp [Kind.shift]; ring
    | inr e =>
      rw [opposite_line_site h e] at hx
      have hE := C.even
      have he := shorter C x
      have hi : res C x=C.half.val := by omega
      apply sub_left_injective (b := C.baseLine)
      change level C x - C.baseLine = x - _
      rw [← line_relation, ← line_relation, opposite_line_site h e]
      rw [show n.val - res C x = res C x by omega]

-- Inner direction classification supports strict gauges, no seam tangents in probes.
lemma next {x} (hx : res C x+1 < n.val) : res C (x+1) = res C x+1 := ofLevel C (x+1) _ _ hx
  (by rw [Nat.cast_add,line_relation]; push_cast; ring) rfl

lemma strict_thread {x : Per n} (hx : Plus C x) (ht : Plus C (x+1)) : bridge C x := by
  have he : res C x +1 < n.val := by have := Kind.strict_lt hx; have := C.even; omega
  unfold bridge; cases H:C.kind with
  | site => exact Kind.strict_lt hx -- defeq?
  | link => exact next he ▸ Kind.strict_lt ht

lemma thread_ends {x : Per n} (hx : bridge C x) : ¬ Plus C (level C x) ∧ ¬ Plus C (level C (x+1)) := by
  have he := C.even
  change res C x + C.kind.shift < C.half.val at hx
  cases h : C.kind with
  | site =>
    rw [h] at hx; change res C x < C.half.val at hx
    constructor
    · rcases Nat.eq_zero_or_pos (res C x) with e|e
      · rw [show level C x=x from by rw [← toRealSide C x,e,level,h]; simp [Kind.shift]; ring]
        simp [Plus, h, e, Kind.Strict]
      exact opposite_leaf (by rw [Plus,h]; exact ⟨e,hx⟩)
    rw [Plus,h,opposite_line_site h (by rw [next (by omega : res C x+1 < n.val)]; omega), next (by omega)]
    unfold Kind.Strict; omega
  | link =>
    rw [h] at hx; simp only [Kind.shift] at hx
    constructor
    · apply opposite_leaf; rw [Plus,h]; exact lt_trans (Nat.lt_succ_self _) hx
    apply opposite_leaf; rw [Plus,h,next (by omega)]; exact hx

-- Link-cut gates, distinguish by which side finishes before crossing.
namespace Link
variable (h : C.kind = .link)

theorem exitRank : res C (C.baseLine+(C.half.val:Per n)-1)+1=C.half.val := by
  have hp : 1≤C.half.val := C.half.property
  have he := C.even
  rw [show C.baseLine+(C.half.val:Per n)-1 = C.baseLine+(((C.half.val-1:ℕ) : Per n)) by
    rw [Nat.cast_sub hp]; push_cast; ring, trivialRes C _ (by omega)]; omega

theorem entryRank : res C (C.baseLine-1)+1=n.val := by
  have hz : 0<n.val := n.property
  rw [show C.baseLine-1=C.baseLine+(((n.val-1 : ℕ)) : Per n) by rw [three _ hz]; simp; ring, trivialRes C _
    (Nat.sub_lt n.property Nat.zero_lt_one)]; omega

def bottom (C : Cut n) : Per n := C.baseLine-1
def top (C : Cut n) : Per n := C.baseLine + C.half.val-1

theorem piers_split : bottom C≠top C := by
  intro H
  have hv : res C (bottom C)+1=n.val := entryRank (C := C)
  have hx : res C (top C)+1=C.half.val := exitRank (C := C)
  rw [H] at hv; have := C.even; have := C.half.property; omega

include h
theorem br : imageChord C (bottom C) = bottom C := by unfold bottom imageChord level; simp [h,Kind.shift]; ring

theorem tr : imageChord C (top C) = top C := by
  unfold top imageChord level
  have ht := C.zeroLength
  rw [two_mul] at ht
  have hs : ((C.half.val:Per n)) = - (C.half.val:Per n) := eq_neg_of_add_eq_zero_left ht
  rw [h]; simp only [Kind.shift, Nat.cast_one];
  nth_rw 1 [hs]; ring

lemma below_base : ¬ Plus C (bottom C) ∧ Plus C (bottom C + 1) := by
  have he := C.even
  refine ⟨?_, ?_⟩
  · intro he'; have hv := Kind.strict_lt he'
    have ht : res C (bottom C)+1=n.val := entryRank (C := C)
    have := C.half.property
    omega
  rw [Plus,h,bottom]; simp [Kind.Strict,res]

lemma leaving_top : Plus C (top C) ∧ ¬ Plus C (top C+1) := by
  have he : res C (top C)+1=C.half.val := exitRank (C := C)
  have hl : Plus C (top C) := by rw [Plus,h]; unfold Kind.Strict; omega
  refine ⟨hl,?_⟩; intro hu
  have hs := opposite_leaf hu
  rw [chord_end,tr h] at hs; exact hs hl

lemma gates : gate C = {bottom C,top C} := by
  have he : res C (bottom C)+1=n.val := entryRank (C := C)
  have hl : res C (top C)+1=C.half.val := exitRank (C := C)
  have hu := C.even; have hh := C.half.property
  ext x; constructor
  · rintro ⟨hp,hP⟩
    have ht := shorter C x
    unfold bridge at hp hP; rw [h] at hp hP; simp only [Kind.shift] at hp hP
    by_cases hx : res C x +1 = n.val
    · rw [show x = bottom C from by
        rw [← toRealSide C x, ← show C.baseLine + (res C x : Per n) = bottom C by
          rw [show res C x=res C (bottom C) by omega,toRealSide]]]; simp
    rw [opposite_wire_link h (by omega)] at hP
    rw [show x=top C from by calc
      _ = _ := (toRealSide C x).symm
      _ = _ := by rw [show res C x=res C (top C) by omega,toRealSide]]
    simp
  intro ht; rcases ht with ht|ht
  · subst x; change ¬bridge C _ ∧ ¬bridge C _; rw [br h]; unfold bridge; rw [h]; simp only [Kind.shift]; omega
  rw [show x=top C from ht]; change ¬bridge C _ ∧ ¬bridge C _; rw [tr h]; unfold bridge; rw [h]; simp only [Kind.shift]; omega
end Link
end YM.Slice
