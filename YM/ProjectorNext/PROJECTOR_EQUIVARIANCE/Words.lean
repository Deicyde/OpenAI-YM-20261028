import YM.Next.FOUNDATIONS.Regular
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Sides
import YM.Work.B16

/-!
# Pricing reorientations: word calculus

Collect right derivatives to the FRONT, without disturbing the left
subsequence. Then, at that config, turn each of the right derivatives into a
left derivative using physical Ad; commute the resulting (fixed!) left
derivative past remaining outer right derivatives too. Result reverses the
order of the right subword. Only use at good points through order k.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Lattice Wilson RG Analysis Next.Foundations
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Config G n → Y} {U : Config G n}

abbrev program (G : Gauge) (n : Side) := List (Instruction G n)

/-- The one-side subprogram. -/
def dispatch (b : Bool) (l : List (Directions G n)) : program G n := l.map (fun i => (b,i))

def partitionSide (b : Bool) : program G n → List (Directions G n)
  | [] => []
  | i :: l => if b=i.1 then i.2 :: partitionSide b l else partitionSide b l

lemma side_length (l : program G n) : (partitionSide true l).length + (partitionSide false l).length = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih => cases i with
    | mk p i => cases p <;> simp only [List.length_cons,partitionSide,reduceCtorEq,↓reduceIte] <;> omega

lemma HasOrderAt.fewer {k l : ℕ} (hl : l ≤ k) (h : HasOrderAt f U k) : HasOrderAt f U l :=
  (ContDiffAt.of_le (show ContDiffAt _ (k:WithTop ℕ∞) _ _ from h) (Nat.cast_le.mpr hl))

lemma word_left (l : List (Directions G n)) : leftDerivs f l = word (dispatch false l) f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    ext1 U
    simp only [leftDerivs,ih]; rfl

/-- Push a left operator past a right subword. No global smoothness, so
carry it even when differentiating at nearby increments. -/
lemma slides_op (x : Directions G n) (l : List (Directions G n)) (z : program G n)
    (h : HasOrderAt f U (l.length + z.length + 1)) :
    word ((false,x) :: (dispatch true l ++ z)) f U = word (dispatch true l ++ ((false,x)::z)) f U := by
  induction l generalizing U with
  | nil => rfl
  | cons i l ih =>
    let K := dispatch true l ++ z
    have hk : K.length + 2 = (i::l).length + z.length + 1 := by simp [K,dispatch]; omega
    have hx : HasOrderAt (word K f) U 2 := smooth_word K (hk.symm ▸ h)
    change opD (false,x) (opD (true,i) (word K f)) U = opD (true,i) (word _ f) U
    rw [op_exchange x i hx]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [h.nearby true i] with t ht
    exact ih (ht.fewer (by simp))

lemma sorted_word (l : program G n) (h : HasOrderAt f U l.length) :
    word l f U = word (dispatch true (partitionSide true l) ++ dispatch false (partitionSide false l)) f U := by
  induction l generalizing U with
  | nil => rfl
  | cons i l ih =>
    let r := partitionSide true l
    let z := dispatch false (partitionSide false l)
    have he : word (i::l) f U = word (i::(dispatch true r ++ z)) f U := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [h.nearby i.1 i.2] with t ht
      exact ih (ht.fewer (by simp))
    rcases i with ⟨a,x⟩; cases a
    · apply he.trans
      have hh : r.length + z.length = l.length := by simpa [z,r,dispatch] using side_length l
      exact (slides_op x r z (h.fewer (by rw [hh]; simp)))
    exact he

lemma collect_left (l : List (Directions G n)) (z : List (Directions G n))
    (h : HasOrderAt f U (l.length+z.length)) :
    word (dispatch true l ++ dispatch false z) f U =
      leftDerivs f (l.reverse.map (leftDir U) ++ z) U := by
  induction l generalizing z with
  | nil => simp only [dispatch,List.map_nil,List.reverse_nil,List.nil_append]; exact (congr_fun (word_left z) U).symm
  | cons i l ih =>
    change opD (true,i) (word (dispatch true l ++ dispatch false z) f) U = _
    rw [op_to_left]
    have ht : l.length + (dispatch false z).length + 1 = (i::l).length+z.length := by simp [dispatch]; omega
    change word ((false,leftDir U i)::(dispatch true l ++ dispatch false z)) f U = _
    rw [slides_op _ _ _ (show HasOrderAt f U _ from h.fewer ht.le)]
    rw [List.reverse_cons,List.map_append,List.append_assoc]
    exact ih (leftDir U i :: z) (h.fewer (by simp; omega))

/-- Exact word normal form at this base: do not move `leftDir U` **inside** a
derivative wrt U. -/
lemma word_equation (l : program G n) (h : HasOrderAt f U l.length) :
    word l f U = leftDerivs f ((partitionSide true l).reverse.map (leftDir U) ++ partitionSide false l) U :=
  (sorted_word l h).trans (collect_left _ _ ((side_length l).symm ▸ h))

section Slot

private lemma head_derivative (x : Directions G n) (h : HasOrderAt f U 1) :
    HasDerivAt (fun t : ℝ => f (increment U (t • x))) (D x (f ∘ increment U) 0) 0 := by
  let p (t : ℝ) := t • x
  have he : HasDerivAt p x 0 := by simpa using (hasDerivAt_id' (0:ℝ)).smul_const x
  have ht : DifferentiableAt ℝ (f ∘ increment U) 0 := by
    apply (show ContDiffAt _ (1:WithTop ℕ∞) _ _ by simpa only [Nat.cast_one] using
      (show ContDiffAt ℝ ((1:ℕ):WithTop ℕ∞) _ _ from h)).differentiableAt one_ne_zero
  apply HasFDerivAt.comp_hasDerivAt (f:=p) (l:=f ∘ increment U) _ _ he
  rw [show p 0 = 0 by simp [p]]; exact ht.hasFDerivAt

/-- Additivity in any ONE slot of left Derivs. -/
lemma slot_add (l r : List (Directions G n)) (a b : Directions G n) (h : HasOrderAt f U (l.length+r.length+1)) :
    leftDerivs f (l ++ ((a+b)::r)) U = leftDerivs f (l ++ (a::r)) U + leftDerivs f (l ++ (b::r)) U := by
  induction l generalizing U with
  | nil =>
    change opD (false,a+b) (leftDerivs f r) U = opD (false,a) (leftDerivs f r) U + opD (false,b) (leftDerivs f r) U
    have he : HasOrderAt (leftDerivs f r) U 1 := by
      rw [word_left]; exact smooth_word (dispatch false r) (by simpa only [dispatch,List.length_map,List.length_nil,Nat.zero_add] using h)
    have ht (z : Directions G n) : opD (false,z) (leftDerivs f r) U = D z _ _ := (head_derivative z he).deriv
    rw [ht,ht,ht]; exact map_add ..
  | cons i l ih =>
    have ht (a : Directions G n) := Next.Foundations.left_has i
      (show (l ++ a::r).length < (i::l).length + r.length + 1 by simp; omega) h
    apply Filter.EventuallyEq.deriv_eq (f:=fun t : ℝ => leftDerivs f (l ++ a::r) (increment U (t • i)) +
      leftDerivs f (l ++ b::r) (increment U (t • i))) _ |>.trans ((ht a).add (ht b)).deriv
    filter_upwards [h.nearby false i] with t hT
    exact ih (hT.fewer (by simp))

/-- Scale every insertion vector. -/
lemma slot_scale (l : List (Directions G n)) (c : ℝ) (h : HasOrderAt f U l.length) :
    leftDerivs f (l.map (c • ·)) U = c^l.length • leftDerivs f l U := by
  induction l generalizing U with
  | nil => simp
  | cons i l ih =>
    change deriv _ 0 = c^(l.length+1) • leftDerivs f (i::l) U
    have he : HasOrderAt (leftDerivs f l) U 1 := by rw [word_left]; exact smooth_word _ (by simpa [dispatch] using h)
    have hd (x : Directions G n) := head_derivative x he
    have hh := (hd (c • i)).const_smul (c^l.length)
    have hx : leftDerivs f (i::l) U = D i _ _ := (hd i).deriv
    rw [hx]
    have hv : c^l.length • D (c • i) (leftDerivs f l ∘ increment U) 0 = c^(l.length+1) • D i (leftDerivs f l ∘ increment U) 0 := by
      unfold D; rw [map_smul,smul_smul,pow_succ]
    rw [← hv]; apply Filter.EventuallyEq.deriv_eq _ |>.trans hh.deriv
    filter_upwards [h.nearby false (c • i)] with t hT
    exact ih (hT.fewer (by simp))
end Slot
end YM.ProjectorNext.Equivariance
