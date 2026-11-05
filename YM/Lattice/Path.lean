import YM.Lattice.Site
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
# Wilson paths

Works at arbitrary scale and on the lattice cover, using the actual directed
step conventions.

Longer kernels keep (path) labels on the cover rather than
measuring just the distance on the torus.
-/

set_option autoImplicit false
namespace YM.Lattice

open Set

/-- Link arrays with positive orientations only. -/
abbrev Links (R K : Type*) := Edge (Four R) → K

structure Step where
  dir : Axis
  neg : Bool
  deriving DecidableEq
abbrev Walk := List Step

def posDir (i : Axis) : Step := ⟨i,false⟩
def negDir (i : Axis) : Step := ⟨i,true⟩
def Step.vec {R : Type*} [AddGroup R] [One R] (d : Step) : Four R :=
  if d.neg then - step d.dir else step d.dir

def Step.rev (d : Step) : Step := ⟨d.dir,!d.neg⟩
def Step.rotate (d : Step) (s : Signed) : Step :=
  ⟨s.perm d.dir,(d.neg).xor (s.flip d.dir)⟩

@[simp] theorem Step.rev_pos (i : Axis) : (posDir i).rev = negDir i := rfl
@[simp] theorem Step.rev_neg (i : Axis) : (negDir i).rev = posDir i := rfl

@[simp] theorem Step.rotate_one (d : Step) : d.rotate 1 = d := by
  rcases d with ⟨i,h|h⟩ <;> rfl

theorem Step.rev_rotate (d : Step) (s : Signed) : d.rev.rotate s = (d.rotate s).rev := by
  rcases d with ⟨i,h|h⟩ <;> simp [rotate, rev]

theorem Step.rotate_mul (d : Step) (s t : Signed) :
    (d.rotate t).rotate s = d.rotate (s*t) := by
  unfold rotate
  rw [Signed.mul_perm_apply]; simp [Signed.mul_flip, Bool.xor_comm (t.flip _)]

variable {R K : Type*} [AddCommGroup R] [One R]

/-- Step's displacement transforms by the same signed permutation. -/
theorem Step.vec_rotate (d : Step) (s : Signed) : (d.rotate s).vec (R := R) = s.act d.vec := by
  rcases d with ⟨i,t⟩
  funext j
  obtain ⟨k,rfl⟩ := s.perm.surjective j
  rw [Signed.act_at]
  by_cases h : k = i
  · subst i
    cases hh : s.flip k <;> cases t <;> simp [vec, rotate, hh]
  · cases hh : s.flip k <;> cases hh' : s.flip i <;> cases t <;> simp [vec, rotate, hh', h]

def Step.used (d : Step) (x : Four R) : Edge (Four R) :=
  if d.neg then (x - step d.dir,d.dir) else (x,d.dir)

/-- Step backwards returns to the same site. -/
theorem Step.vec_rev (d : Step) : d.rev.vec = -(d.vec : Four R) := by
  rcases d with ⟨i,h|h⟩ <;> simp [vec, rev]

def stop (x : Four R) : Walk → Four R
  | [] => x
  | d::w => stop (x+d.vec) w

def visits (x : Four R) : Walk → List (Four R)
  | [] => [x]
  | d::w => x :: visits (x+d.vec) w

theorem stop_append (x : Four R) (a b : Walk) : stop x (a++b) = stop (stop x a) b := by
  induction a generalizing x <;> simp_all [stop]

@[simp] theorem Step.vec_pos (i : Axis) : ((posDir i).vec : Four R) = step i := rfl
@[simp] theorem Step.vec_neg (i : Axis) : ((negDir i).vec : Four R) = - step i := rfl

def square (i j : Axis) : Walk := [posDir i,posDir j,negDir i,negDir j]

@[simp] theorem square_stop (x : Four R) (i j : Axis) : stop x (square i j) = x := by
  simp [stop, square]; abel

variable [Group K]

def Step.read (d : Step) (U : Links R K) (x : Four R) : K :=
  if d.neg then (U (d.used x))⁻¹ else U (d.used x)

@[simp] theorem Step.pos_read (U : Links R K) (x : Four R) (i : Axis) :
    (posDir i).read U x = U (x,i) := rfl
@[simp] theorem Step.neg_read (U : Links R K) (x : Four R) (i : Axis) :
    (negDir i).read U x = (U (x-step i,i))⁻¹ := rfl

@[simp] theorem Step.read_rev (d : Step) (U : Links R K) (x : Four R) :
    d.rev.read U (x + d.vec) = (d.read U x)⁻¹ := by
  rcases d with ⟨i,n|n⟩ <;> simp [read, vec, used, rev, sub_eq_add_neg]

def travel (U : Links R K) (x : Four R) : Walk → K
  | [] => 1
  | d::w => d.read U x * travel U (x + d.vec) w

theorem travel_append (U : Links R K) (x : Four R) (a b : Walk) :
    travel U x (a++b) = travel U x a * travel U (stop x a) b := by
  induction a generalizing x <;> simp_all [travel, stop, mul_assoc]

def reverse (a : Walk) : Walk := a.reverse.map Step.rev

theorem reverse_stop (a : Walk) (x : Four R) : stop (stop x a) (reverse a) = x := by
  induction a generalizing x with
  | nil => simp [stop, reverse]
  | cons d p ih =>
    simp only [reverse, List.reverse_cons, List.map_append, List.map_cons, List.map_nil, stop]
    rw [stop_append, show List.map Step.rev _ = reverse p from rfl, ih]; simp [stop, Step.vec_rev]

theorem travel_reverse (a : Walk) (U : Links R K) (x : Four R) :
    travel U (stop x a) (reverse a) = (travel U x a)⁻¹ := by
  induction a generalizing x with
  | nil => simp [travel, reverse]
  | cons d p ih =>
    simp only [reverse, List.reverse_cons, List.map_append, List.map_cons, List.map_nil, stop]
    rw [travel_append, show List.map Step.rev _ = reverse p from rfl, ih, reverse_stop]
    simp [travel]

/-- Pull under a vertex gauge rotation, including the inverse at the *final* site. -/
def gauge (t : Four R → K) (U : Links R K) : Links R K := fun e =>
  t e.1 * U e * (t (e.1 + step e.2))⁻¹

def GaugeInvariant {X : Type*} (f : Links R K → X) : Prop := ∀ t U, f (gauge t U) = f U

theorem Step.gauge_read (d : Step) (t : Four R → K) (U : Links R K) (x : Four R) :
    d.read (gauge t U) x = t x * d.read U x * (t (x+d.vec))⁻¹ := by
  rcases d with ⟨i,h|h⟩ <;> simp [vec, read, used, gauge, mul_assoc, sub_eq_add_neg]

theorem travel_gauge (t : Four R → K) (U : Links R K) (x : Four R) (w : Walk) :
    travel (gauge t U) x w = t x * travel U x w * (t (stop x w))⁻¹ := by
  induction w generalizing x <;> simp_all [travel, stop, Step.gauge_read, mul_assoc]

def affine (s : Signed) (b x : Four R) : Four R := s.act x + b

def pull (s : Signed) (b : Four R) (U : Links R K) : Links R K :=
  fun e => ((posDir e.2).rotate s).read U (affine s b e.1)

theorem Step.pull_read (d : Step) (U : Links R K) (s : Signed) (b x : Four R) :
    d.read (pull s b U) x = (d.rotate s).read U (affine s b x) := by
  rcases d with ⟨a,h|h⟩
  · rfl
  change (negDir a).read _ _ = ((posDir a).rev.rotate s).read _ _
  rw [Step.neg_read, rev_rotate, pull]
  rw [show affine s b x = affine s b (x-step a) + ((posDir a).rotate s).vec by
    rw [Step.vec_rotate, Step.vec_pos]; simp only [affine, s.act_sub]; abel]
  rw [read_rev]

theorem travel_pull (w : Walk) (U : Links R K) (s : Signed) (x b) :
    travel (pull s b U) x w = travel U (affine s b x) (w.map (·.rotate s)) := by
  induction w generalizing x with
  | nil => simp [travel]
  | cons d w ih =>
    simp only [travel, List.map_cons, ih, Step.pull_read]
    rw [Step.vec_rotate, show affine s b (x+d.vec) = affine s b x + s.act d.vec by
      rw [affine, affine, Signed.act_add]; abel]

@[simp] theorem pull_id (U : Links R K) : pull 1 0 U = U := by
  ext ⟨x,i⟩
  simp [pull, affine]

theorem pull_pull (s t : Signed) (a b) (U : Links R K) :
    pull t b (pull s a U) = pull (s*t) (affine s a b) U := by
  funext e
  rcases e with ⟨x,i⟩
  change ((posDir i).rotate t).read (pull s a U) _ = ((posDir i).rotate (s*t)).read U _
  rw [Step.pull_read, Step.rotate_mul, show affine s a (affine t b x) = affine (s*t) (affine s a b) x by
    simp [affine, Signed.act_mul, add_assoc]]

/-- Translations with `translate b U` at `x` equal to `U` at `x+b`. -/
def translate (b : Four R) (U : Links R K) : Links R K := fun e => U (e.1+b,e.2)

theorem pull_one (b : Four R) (U : Links R K) : pull 1 b U = translate b U := by
  funext e
  simp [pull, affine, translate]

/-! Locality and wrap. -/
section
omit [Group K]

def Agrees (X : Set (Four R)) (U V : Links R K) : Prop := ∀ (e : Edge (Four R)),
    e.1 ∈ X → e.1 + step e.2 ∈ X → U e = V e

/-- When the underlying lattice changes, use ALL read endpoints. -/
def LocalOn {B : Type*} (X : Set (Four R)) (F : Links R K → B) : Prop :=
  ∀ U V, Agrees X U V → F U = F V
end

theorem travel_local (x : Four R) (w : Walk) :
    LocalOn { y | y ∈ visits x w } fun U : Links R K => travel U x w := by
  induction w generalizing x with
  | nil => intro U V h; rfl
  | cons d l ih =>
    intro U V h
    have htail (y) (hy : y ∈ visits (x+d.vec) l) : y ∈ visits x (d::l) :=
      List.mem_cons_of_mem x hy
    have hx : x ∈ visits x (d::l) := List.mem_cons_self
    have hd : x+d.vec ∈ visits x (d::l) := htail _ (by cases l <;> simp [visits])
    change travel U x (d::l) = travel V x (d::l)
    have hrest : travel U (x+d.vec) l = travel V (x+d.vec) l :=
      ih (x+d.vec) U V fun e he hh ↦ h e (htail _ he) (htail _ hh)
    simp only [travel, hrest]
    suffices d.read U x = d.read V x by rw [this]
    rcases d with ⟨i,b|b⟩
    · exact h (x,i) hx hd
    change (negDir i).read U x = (negDir i).read V x
    rw [Step.neg_read, Step.neg_read, h (x - step i,i) ?_ ?_]
    · simpa [sub_eq_add_neg, Step.vec] using hd
    · simpa using hx

variable {n : Side}

def expandAt (b : Site n) (U : Links (Per n) K) : Links ℤ K :=
  fun e => U (wrap n e.1 + b,e.2)

theorem expandAt_pull (b a : Site n) (s : Signed) (U : Links (Per n) K) :
    expandAt b (pull s a U) = pull s 0 (expandAt (affine s a b) U) := by
  funext e
  rcases e with ⟨x,i⟩
  simp only [expandAt, pull, posDir, Step.rotate, Step.read, Step.used,
    affine, Signed.act_add, add_zero, Bool.false_xor, wrap_signed]
  split <;> simp [*, add_assoc]
  congr 2
  abel

theorem wrap_vec (n : Side) (d : Step) : wrap n (d.vec : Cover) = d.vec := by
  rcases d with ⟨i,h|h⟩ <;> simp [Step.vec]

theorem travel_at (b : Site n) (U : Links (Per n) K) (x : Cover) (w : Walk) :
    travel (expandAt b U) x w = travel U (wrap n x + b) w := by
  induction w generalizing x with
  | nil => simp [travel]
  | cons d w ih =>
    rw [travel, travel, ih, map_add, wrap_vec, show wrap n x + d.vec + b = wrap n x + b + d.vec by abel]
    suffices d.read (expandAt b U) x = d.read U (wrap n x+b) by rw [this]
    rcases d with ⟨i,h|h⟩ <;> simp [Step.read, Step.used, expandAt, sub_add_eq_add_sub]

theorem expandAt_gauge (t : Site n → K) (U : Links (Per n) K) (b : Site n) :
    expandAt b (gauge t U) = gauge (fun x => t (wrap n x+b)) (expandAt b U) := by
  funext e; simp [expandAt, gauge, add_right_comm]

omit [Group K] in
theorem LocalOn.expandAt {B : Type*} (X : Set Cover) (F : Links ℤ K → B) (h : LocalOn X F)
    (b : Site n) : LocalOn ((fun x => wrap n x + b) '' X)
       (F ∘ expandAt b) := by
  intro U V hh
  apply h
  rintro ⟨x,i⟩ hx hi
  apply hh (wrap n x+b,i) ⟨x,hx,rfl⟩
  exact ⟨x+step i, hi, by simp [add_right_comm]⟩

end YM.Lattice
