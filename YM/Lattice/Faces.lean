import YM.Lattice.Path

/-!
# Face counting and relabelling the oriented square

Symmetries can shift the *base* and invert circulation. For later uses in
probability and masks we verify the behaviour of real unoriented face invariants.
-/

set_option autoImplicit false
namespace YM.Lattice

abbrev PlaqAxes := {x : Axis × Axis // x.1 < x.2}
abbrev Face (R : Type*) := Four R × PlaqAxes

namespace PlaqAxes

def ordered (a b : Axis) (h : a ≠ b) : PlaqAxes :=
  ⟨(min a b,max a b), by
    rcases lt_or_gt_of_ne h with h|h
    · simpa [h.le] using h
    simpa [h.le] using h ⟩

def rotate (s : Signed) (q : PlaqAxes) : PlaqAxes :=
  ordered (s.perm q.val.1) (s.perm q.val.2) (s.perm.injective.ne q.property.ne)

@[simp] theorem rotate_inv (s : Signed) (q : PlaqAxes) : rotate s⁻¹ (rotate s q) = q := by
  rcases q with ⟨⟨a,b⟩,hq⟩
  change a < b at hq
  rcases lt_or_gt_of_ne (s.perm.injective.ne hq.ne) with h|h
  · apply Subtype.ext
    simp only [rotate, ordered, min_eq_left h.le, max_eq_right h.le, s.inv_perm]
    simp [hq.le]
  apply Subtype.ext
  simp only [rotate, ordered, min_eq_right h.le, max_eq_left h.le, s.inv_perm]
  simp [hq.le]

def transform (s : Signed) : Equiv.Perm PlaqAxes where
  toFun := rotate s
  invFun := rotate s⁻¹
  left_inv := rotate_inv _
  right_inv := by intro q; simpa using rotate_inv s⁻¹ q
end PlaqAxes

variable {R K : Type*} [AddCommGroup R] [One R] [Group K]

def faceValue (U : Links R K) (p : Face R) := travel U p.1 (square p.2.val.1 p.2.val.2)

@[simp] theorem face_gauge (t : Four R → K) (U : Links R K) (p : Face R) :
    faceValue (gauge t U) p = t p.1 * faceValue U p * (t p.1)⁻¹ := by
  simp [faceValue, travel_gauge]

namespace Step
@[simp] theorem rev_rev (a : Step) : a.rev.rev = a := by rcases a with ⟨d,h|h⟩ <;> rfl
end Step

def oriented (a b : Step) : Walk := [a,b,a.rev,b.rev]

@[simp] theorem stop_oriented (a b : Step) (x : Four R) : stop x (oriented a b) = x := by
  simp [oriented, stop, Step.vec_rev]; abel

theorem oriented_swap (a b : Step) (x : Four R) (U : Links R K) :
    travel U x (oriented b a) = (travel U x (oriented a b))⁻¹ := by
  rw [← travel_reverse _ U, reverse, stop_oriented]
  simp only [oriented, List.reverse_cons, List.reverse_nil,
    List.map_cons, List.map_nil, Step.rev_rev, List.nil_append, List.cons_append]

/-- Starting a square at the next corner cyclically conjugates its transport. -/
theorem oriented_next (a b : Step) (x : Four R) (U : Links R K) :
    travel U (x+a.vec) (oriented b a.rev) = (a.read U x)⁻¹ * travel U x (oriented a b) * a.read U x := by
  rw [show oriented b a.rev = [b,a.rev,b.rev] ++ [a] by simp [oriented], travel_append]
  have h : stop (x+a.vec) [b,a.rev,b.rev] = x := stop_oriented a b x
  rw [h]; simp [travel, oriented, mul_assoc]

section ClassFn

variable {M : Type*} (price : K → M) (U : Links R K)
variable (hπ : ∀ k, price k⁻¹ = price k) (hconj : ∀ k g, price (g*k*g⁻¹)=price k)

include hπ hconj in
theorem price_flip (a b : Step) (x : Four R) :
    price (travel U x (oriented a b)) = price (travel U (x+a.vec) (oriented a.rev b)) := by
  rw [oriented_swap b a.rev, hπ, oriented_next]
  symm
  simpa only [inv_inv] using hconj (travel U x (oriented a b)) (a.read U x)⁻¹

/-- Unsigned positive base, before swapping axes to use increasing order. -/
def atFace (X : Four R) (a b : Step) :=
  X + (if a.neg then a.vec else 0) + (if b.neg then b.vec else 0)

include hπ hconj in
theorem price_shift_pos (a b : Step) (x : Four R) :
    price (travel U x (oriented a b)) = price (travel U (atFace x a b) (square a.dir b.dir)) := by
  have second (i : Axis) (v : Step) (y : Four R) :
      price (travel U y (oriented (posDir i) v)) =
        price (travel U (atFace y (posDir i) v) (square i v.dir)) := by
    rcases v with ⟨j,d|d⟩
    · simp [atFace, posDir]; rfl
    · change price (travel _ _ (oriented _ (negDir j))) = _
      rw [oriented_swap, hπ, price_flip price U hπ hconj (negDir j) (posDir i), oriented_swap, hπ]
      simp [atFace, posDir, negDir, Step.vec]; rfl
  rcases a with ⟨i,d|d⟩
  · exact second i b x
  · change price (travel _ _ (oriented (negDir i) b)) = _
    rw [price_flip price U hπ hconj, Step.rev_neg]
    simpa only [atFace, negDir, posDir, Bool.false_eq_true, ↓reduceIte, add_zero] using
      second i b (x+(negDir i).vec)
end ClassFn

namespace Face

def lower (p : Face R) (s : Signed) (t : Four R) : Four R := atFace (affine s t p.1)
  ((posDir p.2.val.1).rotate s) ((posDir p.2.val.2).rotate s)

def send (s : Signed) (t : Four R) (p : Face R) : Face R :=
  (lower p s t, p.2.rotate s)

/-- Shifts in bases do not affect face counts. -/
theorem injective_send (s : Signed) (t : Four R) : Function.Injective (send s t) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  have he : i = j := (PlaqAxes.transform s).injective (congr_arg Prod.snd h)
  subst j
  suffices a = b by rw [this]
  have hd : (send s t (a,i)).1 = (send s t (b,i)).1 := congr_arg Prod.fst h
  simp only [send, lower, atFace, affine, add_left_inj] at hd
  exact s.act_injective hd

theorem send_price (U : Links R K) (p : Face R) (s : Signed) (t : Four R)
    {M : Type*} (price : K → M) (hπ : ∀ k, price k⁻¹ = price k)
    (hconj : ∀ k g, price (g*k*g⁻¹)=price k) :
    price (faceValue (pull s t U) p) = price (faceValue U (send s t p)) := by
  let a := p.2.val.1
  let b := p.2.val.2
  rw [faceValue, travel_pull]
  rw [show List.map _ (square p.2.val.1 p.2.val.2) = oriented ((posDir a).rotate s) ((posDir b).rotate s) by
    rw [show square _ _ = oriented (posDir a) (posDir b) from rfl, oriented, oriented]; simp [← Step.rev_rotate]]
  rw [price_shift_pos price U hπ hconj]
  rcases lt_or_gt_of_ne (show s.perm a ≠ s.perm b from s.perm.injective.ne p.2.property.ne) with h|h
  · change price (travel U _ (square (s.perm a) (s.perm b))) = price (travel U _ (square (min _ _) (max _ _)))
    rw [min_eq_left h.le, max_eq_right h.le]; rfl
  · change price (travel U _ (oriented (posDir (s.perm a)) (posDir (s.perm b)))) =
      price (travel U _ (oriented (posDir (min _ _)) (posDir (max _ _))))
    rw [min_eq_right h.le, max_eq_left h.le, oriented_swap]; rw [hπ]; rfl
end Face
end YM.Lattice
