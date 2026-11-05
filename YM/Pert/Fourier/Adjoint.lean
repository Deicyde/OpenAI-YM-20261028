import YM.Pert.Lattice.Precision
/-! Precision in Feynman gauge via exact summation by parts. -/
noncomputable section
namespace YM.Pert.Orb
open Lattice Function BigOperators
variable {n : Side} {V : Type*}
section
variable [AddCommGroup V]
def ahead (i : Axis) (F : Site n → V) (x : Site n) := F (x+step i)-F x
def past (i : Axis) (F : Site n → V) (x : Site n) := F x-F (x-step i)

def row (A : Orb.Links n → V) (i : Axis) (x : Site n) : V := A (x,i)
lemma ahead_twist (F : Site n → V) (i j : Axis) : past i (ahead j F)=ahead j (past i F) := by
  funext x; unfold ahead past; have eh : x + step j - step i = (x-step i) + step j := by abel
  rw [eh]; exact sub_sub_sub_comm ..
lemma cur_expand (A : Orb.Links n → V) (i j : Axis) (x : Site n) : cur A x i j = ahead i (row A j) x - ahead j (row A i) x := by dsimp [cur,ahead,row]; abel
lemma div_expand (A : Orb.Links n → V) (x) : divB A x = ∑ i : Axis, past i (row A i) x := rfl
lemma lap_expand (F : Site n → V) (x) : lap F x = ∑ i : Axis, past i (ahead i F) x := by unfold lap; apply Finset.sum_congr rfl; intro i _; unfold past ahead; rw [sub_add_cancel]; abel
end

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
def P (F H : Site n → V) := ∑ x : Site n, inner ℝ (F x) (H x)
lemma sub_first (A B C : Site n→V) : P (A-B) C=P A C-P B C := by simp only [P,Pi.sub_apply,inner_sub_left,Finset.sum_sub_distrib]
lemma sub_last (A B C : Site n→V) : P A (B-C)=P A B-P A C := by simp only [P,Pi.sub_apply,inner_sub_right,Finset.sum_sub_distrib]
lemma ahead_adjoint (A B : Site n→V) (i : Axis) : P (ahead i A) B = - P A (past i B) := by
  unfold ahead past; unfold P; simp only [inner_sub_left,inner_sub_right,Finset.sum_sub_distrib,neg_sub]; congr 1
  have he := Equiv.sum_comp (Equiv.addRight (step i)) (fun x : Site n => inner ℝ (A x) (B (x-step i)))
  have hs (r : Site n) : r+step i-step i=r := add_sub_cancel_right ..
  simpa only [show ∀ x : Site n, (Equiv.addRight (step i)) x = x + step i from fun _ => rfl,hs] using he
lemma cancel (A B : Orb.Links n → V) (i j) : P (ahead i (row A j)) (ahead j (row B i)) = P (past j (row A j)) (past i (row B i)) := by
  rw [ahead_adjoint,ahead_twist,show P (row A j) (ahead j _) = P (ahead j (past i (row B i))) (row A j) by unfold P; simp_rw [@real_inner_comm V _ _ ((row A j) _) _]]
  rw [ahead_adjoint,neg_neg]; unfold P; simp_rw [@real_inner_comm V _ _ ((past i (row B i)) _) _]
def PairVal (A B : Orb.Links n → V) (x : Site n) (i j : Axis) := inner ℝ (cur A x i j) (cur B x i j)
lemma pair_swap (A B : Orb.Links n → V) (x : Site n) (i j : Axis) : PairVal A B x i j=PairVal A B x j i := by
  have e (A : Orb.Links n→V) : cur A x i j = -cur A x j i := by rw [cur_expand,cur_expand]; abel
  rw [PairVal,e A,e B,inner_neg_left,inner_neg_right,neg_neg]; rfl
lemma pair_same (A B : Orb.Links n→V) (x : Site n) (i : Axis) : PairVal A B x i i=0 := by simp [PairVal,cur_expand]
lemma half_rows (A B : Orb.Links n→V) (x : Site n) :
   ∑ i : Axis, ∑ j : Axis, PairVal A B x i j = 2*∑ i, ∑ j, if i<j then PairVal A B x i j else 0 := by
  classical
  rw [two_mul]; conv_rhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
  split
  next h => rw [if_neg (not_lt.mpr (le_of_lt h)),add_zero]
  next h =>
    split
    next => simp [pair_swap]
    next h' => obtain rfl : i=j := le_antisymm (le_of_not_gt h') (le_of_not_gt h); simp [pair_same]
lemma gyro_sum (A B : Orb.Links n → V) :
  ∑ x, ∑ i, ∑ j, (if i<j then inner ℝ (cur A x i j) (cur B x i j) else 0) =
   ∑ i, ∑ j, (P (ahead j (row A i)) (ahead j (row B i))-P (past i (row A i)) (past j (row B j))) := by
  let K (i j : Axis) := P (ahead j (row A i)) (ahead j (row B i))-P (past i (row A i)) (past j (row B j))
  change ∑ x, ∑ i, ∑ j, (if i<j then PairVal A B x i j else 0) = (∑ i, ∑ j, K i j)
  apply mul_left_cancel₀ (b:=∑ x, ∑ i, ∑ j, (if i<j then PairVal A B x i j else 0)) (by norm_num : (2:ℝ)≠0)
  rw [Finset.mul_sum]; conv_lhs => arg 2; intro x; rw [← half_rows]
  rw [Finset.sum_comm]; conv_lhs => arg 2; intro j; rw [Finset.sum_comm]
  rw [two_mul]; conv_rhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
  simp_rw [PairVal,cur_expand]
  change (P ((ahead i (row A j))-(ahead j (row A i))) ((ahead i (row B j))-(ahead j (row B i)))) = _
  rw [sub_first,sub_last,sub_last,cancel,cancel]; dsimp [K]; ring
lemma total (A B : Orb.Links n→V) :
  (∑ x, ∑ i, ∑ j, if i<j then inner ℝ (cur A x i j) (cur B x i j) else 0) + ∑ x, inner ℝ (divB A x) (divB B x) = ∑ x : Site n, -(∑ i : Axis, inner ℝ (A (x,i)) (lap (row B i) x)) := by
  rw [gyro_sum]
  simp_rw [div_expand, sum_inner, inner_sum, lap_expand, inner_sum, ← Finset.sum_neg_distrib]
  conv_lhs => arg 2; rw [Finset.sum_comm]; arg 2; intro i; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_add_distrib,Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_neg_distrib]; change _ + P _ _ = -P (row A i) (past j (ahead j (row B i))); rw [sub_add_cancel, ahead_adjoint]
end YM.Pert.Orb
