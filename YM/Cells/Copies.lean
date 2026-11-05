import YM.Cells.Tiling

/-!
# Full replicas follow positive half transformations

`Q=p` set of positive cells of prescribed band. Translate lower corner, move, then compensate
orientation, both in coordinates and antilinear conjugation. No independence assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells.Tiling
open Function Set Filter MeasureTheory
open Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {G : Gauge} {β : ℝ} (T : Tiling n)

lemma corner_pos : T.starts 0 = T.base := T.starts_zero

@[simp] theorem omega_zero : T.omega 0 = 1 := by
  refine Signed.ext ?_ ?_
  · rfl
  funext i; simp [omega]

@[simp] theorem transport_zero : T.translateBy 0 = 0 := by
  simp [translateBy]; ext i; simp [bias]

@[simp] theorem hand_zero : ¬ T.hand 0 := by simp [hand,Finset.filter_false_of_mem]

@[simp] theorem copy_zero (F : Config G n → ℂ) (U) : T.copy 0 F U = F U := by
  simp [copy]

private lemma shift_turn (p v : T.Cell) (a : Axis) :
    T.translateBy (T.mate p a v) = affine (T.bandCut p a).flip (T.bandCut p a).slide (T.translateBy v) := by
  have h := T.after p a v 0
  simpa only [copyMap,Cut.reflect,affine,Signed.act_zero, zero_add] using h

lemma hand_turn (p v : T.Cell) (a : Axis) : T.hand (T.mate p a v) ↔ ¬ T.hand v := by
  let S := ({i : Axis | (T.omega v).flip i} : Finset _)
  let D := ({i : Axis | (T.omega (T.mate p a v)).flip i} : Finset _)
  have he (i : Axis) (h : i≠a) : i ∈ D ↔ i ∈ S := by simp [S,D,T.flip_off _ _ _ h]
  have ht : a ∈ D ↔ a ∉ S := by simp [S,D,T.flip_here]
  change Odd D.card ↔ ¬ Odd S.card
  by_cases hx : a∈S
  · have hy : a∉D := fun he => ht.mp he hx
    have hD : S=insert a D := by
      ext i; by_cases h : i=a <;> simp [h,hx,he]
    rw [hD,Finset.card_insert_of_notMem hy]; simp only [Nat.odd_iff]; omega
  have hy := ht.mpr hx
  have hD : D=insert a S := by
    ext i; by_cases h : i=a <;> simp [h,hx,hy,he]
  rw [hD,Finset.card_insert_of_notMem hx]; simp only [Nat.odd_iff]; omega

theorem opposite (p v : T.Cell) (a : Axis) (F : Config G n → ℂ) U :
    T.copy (T.mate p a v) F U = star (T.copy v F ((T.bandCut p a).pullC G U)) := by
  classical
  unfold copy Cut.pullC
  rw [pull_pull, ← T.turn,← T.shift_turn]
  by_cases h : T.hand v <;> simp only [T.hand_turn,h,↓reduceIte,star_star,not_false_eq_true, not_true_eq_false]

lemma copies (p) {F : Config G n → ℂ} (h : Interior (T.chamber 0) F) : Interior (T.chamber p) (T.copy p F) := by
  classical
  have he : Interior (T.chamber p) _ := h.unchanged (T.omega p) (T.translateBy p) (T.enumerate p)
  by_cases hp : T.hand p
  · change Interior _ (fun x => T.copy p F x)
    simp only [copy, hp, ↓reduceIte]
    exact he.real
  change Interior _ (fun x => T.copy p F x)
  simp only [copy,hp,↓reduceIte]
  exact he

def plusCells (p : T.Cell) (a : Axis) : Finset T.Cell := Finset.univ.filter fun v =>
  (v a-p a).val<T.widthHalf.val

def minusCells (p : T.Cell) (a : Axis) : Finset T.Cell := Finset.univ \ T.plusCells p a

@[simp] lemma positive_side (p a v) : v∈ T.plusCells p a ↔ (v a-p a).val<T.widthHalf.val := by
  simp [plusCells]
@[simp] lemma negative (p a v) : v∈ T.minusCells p a ↔ v∉ T.plusCells p a := by
  simp [minusCells]

lemma cycles (p a v) : T.mate p a v ∈ T.plusCells p a ↔ v∈ T.minusCells p a := by
  -- use strict link seam flip on coarse torus
  let C := Cut.mk (n := T.period) T.widthHalf T.even Kind.link a (p a)
  -- exactly full interval complement
  have he : T.mate p a v a - p a = -(v a - p a) - 1 := by rw [mate_here]; ring
  rw [negative]
  simp only [positive_side,he]
  set k := (v a - p a).val
  have hb : k < T.period.val := ZMod.val_lt _
  have hw : ZMod.val (-(v a-p a)-1) = T.period.val-(k+1) := by
    have hh : T.period.val - (k+1) < T.period.val := by omega
    rw [← ZMod.val_natCast_of_lt (n := T.period.val) hh]; apply congr_arg ZMod.val
    rw [Nat.cast_sub hb,Nat.cast_succ]; simp [Per,k]; ring
  rw [hw]; rw [T.even] at hb; rw [T.even]; omega

lemma cuts (p : T.Cell) (a : Axis) : Finset.univ = T.plusCells p a ∪ T.minusCells p a := by
  ext i
  simp only [Finset.mem_union,T.negative,Finset.mem_univ]; tauto

lemma splitDisjoint (p : T.Cell) (a : Axis) : Disjoint (T.plusCells p a) (T.minusCells p a) :=
  Finset.disjoint_left.mpr fun _ hi hg => ((T.negative ..).mp hg) hi

lemma switched (p a) (g : T.Cell → ℂ) :
    ∏ i ∈ T.minusCells p a, g i = ∏ i ∈ T.plusCells p a, g (T.mate p a i) := by
  symm
  refine Finset.prod_bij' (fun i _ => T.mate p a i) (fun i _ => T.mate p a i) ?_ ?_
    (fun i _ => T.mate_invol p a i) (fun i _ => T.mate_invol p a i) (fun i _ => rfl)
  · intro i hi; exact (T.negative ..).mpr fun w => (T.negative ..).mp ((T.cycles ..).mp w) hi
  intro i hi; exact (T.cycles ..).mpr hi

def Part (p a) (F : T.Cell → Config G n → ℂ) U := ∏ i ∈ T.plusCells p a, T.copy i (F i) U

theorem partInterior (p a) (F : T.Cell → Config G n → ℂ) (h : ∀ i, Interior (T.chamber 0) (F i)) :
    Interior (T.bandCut p a).sector (T.Part p a F) := by
  refine Interior.combines _ _ ?_
  intro i hi
  exact ((T.copies i (h i)).enlarges (T.within p a i ((T.positive_side ..).mp hi)))

/-- Assign two ordered halves using same candidate orientations. -/
def assign {X : Type*} (p a) (f g : T.Cell → X) (i : T.Cell) := if i∈T.plusCells p a then f i else g (T.mate p a i)

def fullAt (F : T.Cell → Config G n → ℂ) (U : Config G n) := ∏ i, T.copy i (F i) U

theorem reflect_equation (p a F) (Q : T.Cell → Config G n → ℂ) U :
    T.fullAt (T.assign p a F Q) U = T.Part p a F U * star (T.Part p a Q ((T.bandCut p a).pullC G U)) := by
  rw [fullAt,T.cuts p a, Finset.prod_union (T.splitDisjoint p a),T.switched]
  unfold Part
  simp only [star_prod]
  congr 1
  · refine Finset.prod_congr rfl fun b hb => ?_; rw [assign, if_pos hb]
  refine Finset.prod_congr rfl fun b hb => ?_
  have he : T.mate p a b ∉ T.plusCells p a := fun v => ((T.negative ..).mp ((T.cycles ..).mp v)) hb
  rw [assign, if_neg he, mate_invol,T.opposite]
end YM.Cells.Tiling
