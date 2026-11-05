import YM.MultiNext.VACUUM_STABILITY.Words

set_option warningAsError false

/-!
# Keeping complete supports on the scalar cluster ledger
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Vacuum
open RG Lattice Wilson Filter Finset Function MeasureTheory Corona
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I : Type} {n : Side}

namespace Syllable
variable (w : Syllable I)

def ground (X : I → Support n) := w.letters.toFinset.biUnion X

def bill (X : I → Support n) (M : ℕ) := (w.letters.map fun i => coverNumber M (X i)).sum

lemma union_ground (t : Syllable I) (X : I → Support n) :
    (w.join t).ground X = w.ground X ∪ t.ground X := by simp [join,ground,List.toFinset_append,Finset.union_biUnion]

lemma union_bill (t : Syllable I) (X : I → Support n) (M : ℕ) :
    (w.join t).bill X M = w.bill X M + t.bill X M := by simp [join,bill]

lemma words_paid (X : I → Support n) (M : ℕ) (h : ∀ i, (X i).Nonempty) : w.letters.length ≤ w.bill X M := by
  obtain ⟨l,c⟩ := w
  induction l with
  | nil => simp [bill]
  | cons a l ih =>
    have hp := Finset.card_pos.mpr (h a)
    have hh : 0 < coverNumber M (X a) := Nat.pos_of_ne_zero (by
      intro H; have ht := pays (X a) M; rw [H,zero_mul] at ht; omega)
    simp only [bill,List.length_cons,List.map_cons,List.sum_cons] at ih ⊢; omega

lemma weight_expansion (X : I → Support n) (M : ℕ) (f : I → ℝ) (s : ℝ) :
    w.weight (fun i => f i * Real.exp (s*coverNumber M (X i))) = w.weight f * Real.exp (s*w.bill X M) := by
  obtain ⟨l,c⟩ := w; induction l with
  | nil => simp [weight,bill]
  | cons a l ih =>
    simp only [weight,List.map_cons,List.prod_cons,bill,List.sum_cons,Nat.cast_add,mul_add,Real.exp_add] at *
    rw [mul_left_comm ‖c‖,ih,mul_left_comm ‖c‖]; ring
end Syllable

namespace Text
open Syllable
variable (T : Text I)

/-- Anchored at `x` *in the word* and buying the actual connected-cover weight. -/
def Peaked (X : I → Support n) (M : ℕ) (x : Site n) := ∀ i,
    x ∈ (T.line i).ground X ∧ coverNumber M ((T.line i).ground X) ≤ (T.line i).bill X M

/-- Used between anchored words; the roots of these might be disconnected, but will be linked by Y. -/
def Sticky (X : I → Support n) (M : ℕ) (Y : Support n) := ∀ i, ∀ Z : Support n, Y ⊆ Z →
    coverNumber M (Z ∪ (T.line i).ground X) ≤ coverNumber M Z + (T.line i).bill X M

variable {T} {V : Text I} {X : I → Support n} {M : ℕ} {Y : Support n} {x : Site n}

lemma Peaked.sticky (h : T.Peaked X M x) (hy : x ∈ Y) : T.Sticky X M Y := by
  intro i Z hz; exact (Corona.meets_sum (hz hy) (h i).1 M).trans (Nat.add_le_add_left (h i).2 _)





lemma peak_atom {i : I} (hx : x ∈ X i) : (atom i).Peaked X M x := by
  intro a; simp [atom,Syllable.ground,Syllable.bill,hx]

lemma Sticky.scale (h : T.Sticky X M Y) (z : ℂ) : (T.scale z).Sticky X M Y := h

lemma Sticky.pair (hT : T.Sticky X M Y) (hV : V.Sticky X M Y) : (T.pair V).Sticky X M Y := by
  unfold Sticky Text.pair; rintro ⟨i,j⟩ Z hz
  simp only [union_bill,union_ground]
  rw [← Finset.union_assoc,← Nat.add_assoc]
  exact ((hV j _ (subset_trans hz Finset.subset_union_left))).trans (Nat.add_le_add_right (hT i _ hz) _)

lemma Sticky.copies (h : T.Sticky X M Y) (k : ℕ) : (T.copies k).Sticky X M Y := by
  induction k with
  | zero => simp [Text.copies,Sticky,ground,bill]
  | succ _ ih => simp only [Text.copies]; exact ih.pair h

lemma Sticky.expanding (h : T.Sticky X M Y) : T.expanding.Sticky X M Y := fun i =>
    ((h.copies i.1).scale _ ) i.2

lemma atom_adjoined {i : I} (hx : x ∈ X i) (h : V.Sticky X M (X i)) : ((atom i).pair V).Peaked X M x := by
  intro a; obtain ⟨r,j⟩ := a
  have hs := h j (X i) le_rfl
  simp only [pair,union_ground,union_bill]
  refine ⟨mem_union_left _ ((peak_atom (M:=M) hx) r).1,?_⟩
  simpa [atom,ground,bill] using hs

lemma Peaked.pair (h : T.Peaked X M x) (h' : V.Peaked X M x) : (T.pair V).Peaked X M x := by
  intro a; obtain ⟨i,j⟩ := a
  simp only [Text.pair,union_ground,union_bill]; refine ⟨mem_union_left _ (h i).1,?_⟩
  exact (Corona.meets_sum (h i).1 (h' j).1 _).trans (Nat.add_le_add (h i).2 (h' j).2)

lemma Peaked.scale (h : T.Peaked X M x) (z : ℂ) : (T.scale z).Peaked X M x := h

lemma Peaked.more (h : T.Peaked X M x) (k : ℕ) : (T.copies (k+1)).Peaked X M x := by
  induction k with
  | zero =>
    simp only [Text.copies,Peaked]; intro a; obtain ⟨r,j⟩ := a; exact h _
  | succ k ih => nth_rw 1 [Text.copies]; exact ih.pair h

lemma Peaked.pressed (h : T.Peaked X M x) : T.pressed.Peaked X M x := fun i =>
    ((h.more i.1).scale _) i.2
end Text

end YM.Multi.Vacuum
