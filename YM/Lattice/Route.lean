import YM.Lattice.Box

/-! Coordinate route with starting corner retained. -/

set_option autoImplicit false
namespace YM.Lattice

open Finset

@[simp] theorem reverse_append (p q : Walk) : reverse (p++q) = reverse q ++ reverse p := by simp [reverse]

theorem reverse_straight (i : Axis) (d : ℤ) : reverse (straight i d) = straight i (-d) := by
  rcases lt_trichotomy d 0 with h|h|h
  all_goals simp [*,straight, reverse, Step.rev]
  all_goals omega

theorem axisRoute_append (p q : List Axis) (x y) : axisRoute x y (p++q)=axisRoute x y p++axisRoute x y q := by simp [axisRoute]

theorem axisRoute_reverse (l : List Axis) (x y) : axisRoute y x l.reverse = reverse (axisRoute x y l) := by
  induction l with
  | nil => simp [reverse,axisRoute]
  | cons a l ih => rw [List.reverse_cons,axisRoute_append,ih]; simp [axisRoute,reverse_straight]

lemma rev_range : (List.finRange 4).map Fin.rev = (List.finRange 4).reverse := by decide

def backward (o : Lattice.Order) : Lattice.Order := (Fin.revPerm).trans o

@[simp] theorem backward_back (o : Lattice.Order) : backward (backward o) = o := by ext; simp [backward]

def backOrder : Equiv.Perm Lattice.Order := ⟨backward,backward, backward_back, backward_back⟩

theorem back_axes (o : Lattice.Order) : allAxes (backOrder o) = (allAxes o).reverse := by
  unfold allAxes
  rw [← List.map_reverse, ← rev_range, List.map_map]; rfl

theorem back_route (x y) (o : Lattice.Order) : route x y (backOrder o) = reverse (route y x o) := by
  unfold route; rw [back_axes, axisRoute_reverse]

lemma indexRoute (d : ℤ) (a : Axis) (s : Signed) : List.map (·.rotate s) (straight a d) =
    straight (s.perm a) (if s.flip a then -d else d) := by
  cases hf : s.flip a <;> rcases lt_trichotomy d 0 with h|h|h
  all_goals simp [*,straight,Step.rotate]
  all_goals omega

def sendOrder (s : Signed) (o : Lattice.Order) : Lattice.Order := o.trans s.perm

@[simp] lemma sendOrder_inv (s : Signed) (o : Lattice.Order) : sendOrder s⁻¹ (sendOrder s o) = o := by ext; simp [sendOrder,Signed.inv_perm]

def orderEquiv (s : Signed) : Equiv.Perm Lattice.Order where
  toFun := sendOrder s
  invFun := sendOrder s⁻¹
  left_inv := sendOrder_inv s
  right_inv := by intro h; simpa using sendOrder_inv s⁻¹ h

theorem send_route (x y) (o : Lattice.Order) (s : Signed) (b) :
    List.map (·.rotate s) (route x y o) = route (affine s b x) (affine s b y) (orderEquiv s o) := by
  have he : allAxes (orderEquiv s o) = List.map s.perm (allAxes o) := by unfold allAxes; rw [List.map_map]; rfl
  unfold route; rw [he]; unfold axisRoute; rw [List.map_flatMap,List.flatMap_map]; congr 1
  funext i
  rw [indexRoute]; simp only [affine, Pi.add_apply, s.act_at, add_sub_add_right_eq_sub]
  split <;> simp [*, sub_neg_eq_add]; congr 1; abel
end YM.Lattice
