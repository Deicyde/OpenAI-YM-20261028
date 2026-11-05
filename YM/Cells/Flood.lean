import YM.Cells.Copies

/-!
# Finite flood, no dyadic assumptions

Independent of gauge fields. Odd/even seam placement geometry handled in Copy.
If folds preserve a predicate of assignments, some homogeneous assignment has it.
We need copy one way (all translated seams). Start with one slice,
extend backwards until there is a half, then finish, preserving earlier axes.
-/
set_option autoImplicit false
namespace YM.Cells.Tiling
open Function Set Filter MeasureTheory
open Lattice Wilson
variable {n : Side} (T : Tiling n) {α : Type*} (Q : (T.Cell → α) → Prop)

/-- Slices identical in a whole-axis direction. -/
def equalSlices (F : T.Cell → α) (a : Axis) := ∀ x y : T.Cell, (∀ i : Axis, i ≠ a → x i=y i) → F x=F y

def strip (F : T.Cell → α) (p : T.Cell) (a : Axis) (h : ℕ) :=
    ∀ x y : T.Cell, (x a-p a).val<h → (y a-p a).val<h →
    (∀ b : Axis, b≠a → x b=y b) → F x=F y

def Reflects := ∀ p a (F : T.Cell → α), Q F → Q (T.assign p a F F)

lemma keep_axis (p a F) (b : Axis) (h : b≠a) (e : T.equalSlices (α := α) F b) :
    T.equalSlices (T.assign p a F F) b := by
  intro x y he
  have hu := he a h.symm
  have hx : x ∈ T.plusCells p a ↔ y∈ T.plusCells p a := by simp [hu]
  unfold assign; split
  next hh => rw [if_pos (hx.mp hh), e _ _ he]
  next hh =>
    rw [if_neg (mt hx.mpr hh)]
    apply e
    intro i hi
    by_cases hp : i=a
    · subst i; rw [mate_here, mate_here,hu]
    rw [mate_off T p a x hp,mate_off T p a y hp,he _ hi]

lemma extend_half (p : T.Cell) (a : Axis) {h : ℕ} (he : 0 < h) (hH : h ≤ T.widthHalf.val) (F : T.Cell → α)
    (H : T.strip F p a h) :
    T.strip (T.assign p a F F) (update p a (p a-1)) a (h+1) := by
  let X (x : T.Cell) := if x ∈ T.plusCells p a then x else T.mate p a x
  have hi (x : T.Cell) (hx : (x a-(p a-1)).val<h+1) : (X x a-p a).val<h  := by
    set i := (x a-(p a-1)).val with hi
    have heq : x a = p a-1 + (i : Per T.period) := by simp [hi,Per]
    rcases Nat.eq_zero_or_pos i with hk|hk
    · have ht : x a=p a-1 := by rw [heq, hk,Nat.cast_zero, add_zero]
      have hy : T.mate p a x a-p a=0 := by rw [mate_here,ht]; ring
      dsimp only [X]
      rw [if_neg]
      · rw [hy, ZMod.val_zero]; exact he
      refine (T.negative ..).mp ((T.cycles ..).mp ?_)
      rw [T.positive_side,hy]; exact lt_of_le_of_lt (Nat.le_of_eq (ZMod.val_zero ..)) T.widthHalf.property
    have HW : i-1 < h := by omega
    have hv : x a-p a = ((i-1 : ℕ) : Per T.period) := by
      rw [heq,Nat.cast_sub hk]; push_cast; ring
    have hh : (x a-p a).val=i-1 := by rw [hv, ZMod.val_natCast_of_lt (lt_of_lt_of_le (HW.trans_le hH)
      (by rw [T.even]; omega))]
    dsimp only [X]
    rw [if_pos ((T.positive_side ..).mpr ((hh.symm ▸ HW).trans_le hH)),hh]; exact HW
  have hx (x : T.Cell) (b : Axis) (h : b ≠ a) : X x b = x b := by
    dsimp only [X]; split; rfl; exact mate_off _ _ _ _ h
  have hy (x : T.Cell) : T.assign p a F F x = F (X x) := by unfold assign X; split <;> rfl
  intro v w hv hw hg
  rw [hy, hy]
  apply H _ _ (hi v (by simpa using hv)) (hi w (by simpa using hw))
  exact fun b hb => (hx _ b hb).trans ((hg b hb).trans (hx _ b hb).symm)

lemma flood_axis (R : T.Reflects Q) (A : Finset Axis) (a : Axis) (hw : a ∉ A)
    (F : T.Cell → α) (hf : Q F) (h : ∀ b ∈ A, T.equalSlices F b) :
    ∃ G, Q G ∧ ∀ b ∈ insert a A, T.equalSlices G b := by
  have he (n) (hn : n < T.widthHalf.val) : ∃ G p, Q G ∧ (∀ b ∈ A, T.equalSlices G b) ∧ T.strip G p a (n+1) := by
    induction n with
    | zero =>
      refine ⟨F,0,hf,h,?_⟩
      intro x y hx hy hu
      have hi : x a=y a := by
        have he (x : T.Cell) (H : (x a - (0 : T.Cell) a).val < 1) : x a=0 := by
          have ht : (x a - (0 : T.Cell) a).val=0 := by omega
          simpa using ht
        rw [he _ hx, he _ hy]
      congr 1
      funext i; rcases eq_or_ne i a with w|w
      · rw [w, hi]
      exact hu i w
    | succ n ih =>
      obtain ⟨B,p,hp,hB,H⟩ := ih (by omega)
      exact ⟨_,_,R p a B hp,fun b hb => T.keep_axis _ _ _ _ (ne_of_mem_of_not_mem hb hw) (hB b hb),
        T.extend_half p a (Nat.succ_pos _) (by omega) B H⟩
  have hz : 1 ≤ T.widthHalf.val := T.widthHalf.property
  obtain ⟨G,p,hp,hG,H⟩ := he (T.widthHalf.val-1) (Nat.sub_lt T.widthHalf.property Nat.zero_lt_one)
  rw [Nat.sub_add_cancel hz] at H
  refine ⟨_,R p a G hp,?_⟩
  intro b hb; rcases Finset.mem_insert.mp hb with h|h
  · subst b
    intro x y he
    let Y (x : T.Cell) := if x∈T.plusCells p a then x else T.mate p a x
    have hh (x : T.Cell) : Y x∈T.plusCells p a := by
      unfold Y; split_ifs with hh; exact hh; exact (T.cycles ..).mpr ((T.negative ..).mpr hh)
    have hw (x : T.Cell) (i) (hv : i≠a) : Y x i = x i := by unfold Y; split_ifs <;> simp [hv]
    have hu (x : T.Cell) : T.assign p a G G x = G (Y x) := by unfold assign Y; split <;> rfl
    rw [hu,hu]
    exact H _ _ ((T.positive_side ..).mp (hh _)) ((T.positive_side ..).mp (hh _))
      fun i hi => (hw x i hi).trans ((he i hi).trans (hw y i hi).symm)
  exact T.keep_axis _ _ _ _ (ne_of_mem_of_not_mem h hw) (hG b h)

/-- There is a homogeneous assignment for any fold-closed predicate already met. -/
theorem existence (H : T.Reflects Q) (f : T.Cell → α) (hf : Q f) : ∃ c, Q fun _ => c := by
  have he (A : Finset Axis) : ∃ G, Q G ∧ ∀ b ∈ A, T.equalSlices G b := by
    induction A using Finset.induction_on with
    | empty => exact ⟨f,hf,by simp⟩
    | @insert i S hi hs =>
      obtain ⟨G,hg,hS⟩ := hs
      exact T.flood_axis Q H _ i hi G hg hS
  obtain ⟨G,hg,hS⟩ := he Finset.univ
  refine ⟨G 0,?_⟩
  convert hg using 1
  funext v
  let X (A : Finset Axis) (i : Axis) := if i∈A then v i else 0
  have Hx (A : Finset Axis) : G (X A) = G 0 := by
    induction A using Finset.induction_on with
    | empty => simp only [X,Finset.notMem_empty,↓reduceIte]; rfl
    | @insert i s h hv =>
      rw [← hv]; apply hS _ (Finset.mem_univ i)
      intro b he; simp [X,he]
  exact Eq.symm (show G v = G 0 by rw [← Hx Finset.univ]; simp [X])
end YM.Cells.Tiling
