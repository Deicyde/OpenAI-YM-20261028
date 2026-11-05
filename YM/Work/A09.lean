import YM.Bid.Angular

set_option autoImplicit false
noncomputable section
namespace YM.Work.A09
open Bid Org Table Ward Spin
open Ortho (plane Skew)
open scoped BigOperators Matrix.Norms.Frobenius

lemma bracket_planes (a b i j : Axis) :
    bracket (plane a b) (plane i j) = (if b = i then plane a j else 0) -
      (if b = j then plane a i else 0) + (if a = i then plane j b else 0) -
      (if a = j then plane i b else 0) := by
  apply Subtype.ext
  split_ifs <;>
    simp_all [bracket, plane, sub_mul, mul_sub, eq_comm] <;> abel

lemma bracket_pick (p : Ind) : bracket (Spin.K (fle p)) (Spin.K (fox p)) = Spin.K p := by
  obtain ⟨i,j⟩ := p
  have hn : pick (i,j) ≠ i ∧ pick (i,j) ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  change bracket (plane i (pick _)) (plane (pick _) j) = plane i j
  rw [bracket_planes]
  have hz (b : Axis) : plane b b = 0 := Subtype.ext (by simp [plane])
  simp [hn.1.symm, hn.2, hz]

section ring
variable {R : Type*} [Ring R] (f : Skew →+ R)
    (h : ∀ u v, f u * f v - f v * f u = f (bracket u v))
include h

lemma perfect : ∀ i, f (Spin.K i) = f (Spin.K (fle i)) * f (Spin.K (fox i)) - f (Spin.K (fox i)) * f (Spin.K (fle i)) := fun i =>
  (h (Spin.K (fle i)) (Spin.K (fox i)) |>.trans (congr_arg f (bracket_pick i))).symm

lemma casimir (p : Ind) : Commute (∑ q : Ind, f (Spin.K q)^2) (f (Spin.K p)) := by
  obtain ⟨i,j⟩ := p
  let P (a b : Axis) := f (plane a b)
  let g (a b : Axis) := (if b=i then P a j else 0) - (if b=j then P a i else 0) +
    (if a=i then P j b else 0) - (if a=j then P i b else 0)
  have hg (a b : Axis) : P a b * P i j - P i j * P a b = g a b := by
    dsimp [P]; rw [h, bracket_planes]; simp [P, g, apply_ite f]
  have he (a b : Axis) : P a b^2 * P i j - P i j * P a b^2 = P a b * g a b + g a b * P a b := by
    rw [← hg]; noncomm_ring
  change (∑ q : Ind, P q.1 q.2 ^ 2) * P i j = P i j * (∑ q : Ind, P q.1 q.2 ^ 2)
  rw [Fintype.sum_prod_type]
  dsimp only
  apply sub_eq_zero.mp
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, he]
  simp [g, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel
end ring

variable {G : Gauge} {L : Register G} {S : Table L}

/-- At one cap use the ordinary endomorphism ring with continuous maps. -/
def plain (D : SpinRows S) (d : ℕ) : Skew →+ Mat (S.Field d) :=
  LinearMap.toContinuousLinearMap.toLinearMap.toAddMonoidHom.comp (D d).toAddMonoidHom

lemma plain_bracket (D : SpinRows S) (h : Brackets D) (d : ℕ) (u v : Skew) :
    plain D d u * plain D d v - plain D d v * plain D d u = plain D d (bracket u v) := by
  ext1 x
  exact LinearMap.congr_fun (h d u v) x

/-- Relative infinitesimal, both sides at the same cap. -/
def relative (D T : SpinRows S) (d : ℕ) : Skew →+ Spin.End (S.Field d) where
  toFun u := effect (plain D d u) (plain T d u)
  map_zero' := by rw [map_zero, map_zero]; simp [effect]
  map_add' u v := by
    ext1 x; rw [map_add, map_add, add_apply]
    simp only [atAct, mul_add, add_mul]; abel

lemma relative_bracket (D T : SpinRows S) (h : Brackets D) (k : Brackets T) (d : ℕ) (u v : Skew) :
    relative D T d u * relative D T d v - relative D T d v * relative D T d u = relative D T d (bracket u v) := by
  let F w := effect (plain D d w) (plain T d w)
  ext1 x
  change F u (F v x) - F v (F u x) = F (bracket u v) x
  simp only [F, atAct, ← plain_bracket D h, ← plain_bracket T k]; noncomm_ring

lemma commutes_evaluate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {A B : Spin.End X} (h : Commute A B) (z : List ℝ) : Commute (evaluate z A) B := by
  induction z with
  | nil => exact Commute.zero_left _
  | cons t z ih => exact ((Commute.one_left _).smul_left (t:ℂ)).add_left (h.mul_left ih)

theorem answer : YM.Bid.A09 := by
  intro G L S D h
  constructor
  · intro d; exact perfect (plain D d) (plain_bracket D h d)
  intro T k d z i
  exact commutes_evaluate (casimir (relative D T d) (relative_bracket D T h k d) i) z
end YM.Work.A09
