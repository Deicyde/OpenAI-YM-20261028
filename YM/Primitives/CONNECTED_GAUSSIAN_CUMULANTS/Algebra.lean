import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra

/-!
# Anchoring a Gaussian computation in the existing source algebra

One fused/rooted group of vertices, whose label is a nonempty set `A`.
Outside `A`, for now, each vertex carries its own marker (square-zero but
unordered). When varying the Gaussian law by changing just the couplings
from `A` to the other vertices, take a quotient in THIS algebra. Selecting
terms *before* differentiating it is what will allow a tree calculation,
where the law can be degenerate and some individual moments can vanish. No
division by coefficients at non-quiet modes. `R.Census` may discard many
products due to other exclusion constraints -- never need moments outside a
given allowed target coefficient when computing that coefficient.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
namespace Anchor
open Finset Marker Function YM.Extra.Trajectories
open scoped BigOperators
variable {V : Type*} [DecidableEq V] {R : Census V}

/-- Coordinate ideal: a surviving term must contain all markers of A. -/
def Contains (A : Finset V) (x : Poly R) : Prop := ∀ s : R.Mode, ¬ A ⊆ s.val → x.part s = 0

/-- Besides marking a root, project table arguments to `T`; this truncation
is only algebraic, all actual overlap asks remain outside these weights. -/
def withinSet (T : Finset V) (m : Poly R) : Poly R :=
  Poly.inject fun s => if s.val ⊆ T then m.part s else 0

def without (A : Finset V) (m : Poly R) : Poly R :=
  Poly.inject fun s => if Disjoint s.val A then m.part s else 0

def usingAll (A : Finset V) (m : Poly R) : Poly R :=
  Poly.inject fun s => if A ⊆ s.val then m.part s else 0

def outer (T A : Finset V) (m : Poly R) := without A (withinSet T m)

def root (T A : Finset V) (m : Poly R) := usingAll A (withinSet T m)



lemma outer_part (T A : Finset V) (m : Poly R) (s) :
    (outer T A m).part s = if s.val ⊆ T ∧ Disjoint s.val A then m.part s else 0 := by
  change (if Disjoint .. then if s.val ⊆ T then _ else 0 else 0)=_
  split_ifs <;> simp_all

lemma root_part (T A : Finset V) (m : Poly R) (s) :
    (root T A m).part s = if s.val ⊆ T ∧ A ⊆ s.val then m.part s else 0 := by
  change (if A ⊆ s.val then if s.val ⊆ T then _ else 0 else 0)=_
  split_ifs <;> simp_all

lemma root_contains (T A : Finset V) (m : Poly R) : Contains A (root T A m) :=
  fun s hs => by rw [root_part, if_neg (not_and_of_not_right _ hs)]



lemma Contains.quiet {x : Poly R} {A} (h : Contains A x) (ha : A.Nonempty) : x.part R.quiet=0 := by
  apply h
  exact fun h => ha.ne_empty (subset_empty.mp h)

lemma contains_mul_congr {x y z : Poly R} {A} (h : Contains A x)
    (he : ∀ j : R.Mode, Disjoint j.val A → y.part j=z.part j) : x*y=x*z := by
  ext s; simp_rw [Poly.part_mul]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  split_ifs with hm
  · by_cases hi : A ⊆ i.val
    · rw [he _ (hm.1.symm.mono_right hi)]
    rw [h _ hi, zero_mul, zero_mul]
  rfl



-- Congruences at target subset

def UpTo (T : Finset V) (m n : Poly R) := ∀ i : R.Mode, i.val ⊆ T → m.part i=n.part i

lemma UpTo.add {x y z w : Poly R} {T} (hx : UpTo T x y) (hz : UpTo T z w) : UpTo T (x+z) (y+w) :=
  fun i hi => congr_arg₂ (·+·) (hx i hi) (hz i hi)

lemma UpTo.sub {x y z w : Poly R} {T} (hx : UpTo T x y) (hz : UpTo T z w) : UpTo T (x-z) (y-w) :=
  fun i hi => congr_arg₂ (·-·) (hx i hi) (hz i hi)

lemma UpTo.mul {x y z w : Poly R} {T} (hx : UpTo T x y) (hz : UpTo T z w) : UpTo T (x*z) (y*w) := by
  intro s hs; simp_rw [Poly.part_mul]
  apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
  split_ifs with hm
  · rw [hx _ ((hm.2 ▸ Finset.subset_union_left : i.val ⊆ s.val).trans hs),
        hz _ ((hm.2 ▸ Finset.subset_union_right : j.val ⊆ s.val).trans hs)]
  rfl

lemma UpTo.pow {x y : Poly R} {T} (hx : UpTo T x y) (k : ℕ) : UpTo T (x^k) (y^k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact fun _ _ => rfl
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hx

def Lacks (i : V) (m : Poly R) := ∀ s : R.Mode, i ∈ s.val → m.part s=0





lemma Lacks.mul {i : V} {x y : Poly R} (hx : Lacks i x) (hy : Lacks i y) : Lacks i (x*y) := by
  intro s he
  rw [Poly.part_mul]
  refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => ?_
  split_ifs with hm
  · rw [← hm.2, mem_union] at he
    rcases he with ht|ht
    · rw [hx a ht, zero_mul]
    rw [hy b ht, mul_zero]
  rfl

lemma lacks_one (i : V) : Lacks i (1 : Poly R) := by
  intro s hs
  rw [Poly.one_part, if_neg]
  intro he
  rw [he] at hs
  simp [Census.quiet] at hs

lemma Lacks.pow {i : V} {x : Poly R} (hx : Lacks i x) (j : ℕ) : Lacks i (x^j) := by
  induction j with
  | zero => rw [pow_zero]; exact lacks_one i
  | succ j ih => rw [pow_succ]; exact ih.mul hx



lemma outer_quiet (T A : Finset V) (m : Poly R) : (outer T A m).part R.quiet = m.part R.quiet := by
  rw [outer_part, if_pos]; simp [Census.quiet]

section log
variable [Fintype V]

lemma UpTo.pass {x y : Poly R} {T} (hx : UpTo T x y) : UpTo T (x.pass) (y.pass) := by
  intro s hs
  simp only [Poly.pass, Poly.part_sum, Poly.part_smul]
  apply sum_congr rfl; intro i _
  rw [hx.pow i s hs]

lemma UpTo.conn {x y : Poly R} {T} (hx : UpTo T x y) : UpTo T (connected x) (connected y) := by
  unfold connected
  generalize Fintype.card V=n
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih => unfold iteration; exact ih.add (hx.sub ih.pass)

lemma Lacks.pass {x : Poly R} {i} (hx : Lacks i x) : Lacks i x.pass := by
  intro s hs; simp only [Poly.pass, Poly.part_sum, Poly.part_smul]
  exact sum_eq_zero fun j _ => by rw [hx.pow j s hs,mul_zero]





def inverseMass (m : Poly R) := Poly.pass (-connected m)

lemma right_inverse {m : Poly R} (h : m.part R.quiet=1) : m * inverseMass m = 1 := by
  have hq := connected_quiet h
  unfold inverseMass
  nth_rw 1 [← pass_connected h]
  rw [← pass_add hq (by rw [Poly.part_neg, hq, neg_zero]), add_neg_cancel, pass_zero]



def quotient (T A : Finset V) (m : Poly R) := root T A m * inverseMass (outer T A m)







/-- When varying the root block the denominator was the old outside
moment. On multiplying by a newly merged numerator we may remove the
terms intersecting that new larger block also. -/
lemma change_outer {T A B : Finset V} (h : A ⊆ B) (m n : Poly R)
    (he : ∀ j : R.Mode, j.val ⊆ T → Disjoint j.val B → m.part j=n.part j) :
    root T B n * inverseMass (outer T A m) = quotient T B n := by
  apply contains_mul_congr (root_contains T B n)
  intro j hj
  have ht : UpTo j.val (outer T A m) (outer T B n) := by
    intro s hs
    have hB := hj.mono_left hs
    have hA := hB.mono_right h
    by_cases hi : s.val ⊆ T <;> simp [outer_part, hA, hB, hi]
    exact he s hi hB
  apply UpTo.pass (T:=j.val) _ j (Subset.refl _)
  exact fun s hs => by rw [Poly.part_neg, Poly.part_neg, ht.conn s hs]

/-- Reaching all markers leaves only the numerator. -/
lemma quotient_end (t : R.Mode) (m : Poly R) (hm : m.part R.quiet=1) :
    (quotient t.val t.val m).part t=m.part t := by
  have he : outer t.val t.val m=1 := by
    ext i; rw [outer_part, Poly.one_part]
    by_cases hi : i=R.quiet
    · subst i; rw [if_pos (by simp [Census.quiet]), hm, if_pos rfl]
    rw [if_neg hi, if_neg]; intro hh
    apply hi; apply Subtype.ext; exact eq_empty_iff_forall_notMem.mpr fun v hv => disjoint_left.mp hh.2 hv (hh.1 hv)
  have hO := right_inverse (show (outer t.val t.val m).part R.quiet=1 from (outer_quiet ..).trans hm)
  rw [he,one_mul] at hO
  rw [quotient,he,hO,mul_one,root_part, if_pos (by simp)]

end log

/-- Canonical residual mode in a rooted multiplication. -/
def diff (t : R.Mode) (A : Finset V) : R.Mode := ⟨t.val \ A, R.down t.property _ sdiff_subset⟩

lemma separates (t a : R.Mode) (h : a.val ⊆ t.val) : Poly.merges a (diff t a.val) t := by
  unfold diff Poly.merges
  dsimp only
  exact ⟨disjoint_sdiff, union_sdiff_of_subset h⟩

lemma separates_unique (t a b : R.Mode) (h : Poly.merges a b t) : b=diff t a.val := by
  apply Subtype.ext
  change b.val=t.val \ a.val
  rw [← h.2]
  ext j; simp only [mem_sdiff, mem_union]
  constructor
  · intro hb; exact ⟨.inr hb, fun ha => disjoint_left.mp h.1 ha hb⟩
  exact fun hp => hp.1.resolve_left hp.2

lemma mul_at_part (t a : R.Mode) (x : ℂ) (m : Poly R) :
    ((Poly.send a x) * m).part t =
      if a.val ⊆ t.val then x * m.part (diff t a.val) else 0 := by
  rw [Poly.part_mul, sum_eq_single a]; rotate_left
  · intro b _ h; simp [h]
  · simp
  by_cases h : a.val ⊆ t.val
  · rw [if_pos h, sum_eq_single (diff t a.val)]
    · rw [if_pos (separates _ _ h)]; simp
    · intro b _ hb
      rw [if_neg (mt (separates_unique _ _ b) hb)]
    simp
  rw [if_neg h]
  exact sum_eq_zero fun b _ => by
    rw [if_neg]; intro he
    exact h (he.2 ▸ Finset.subset_union_left)

/-- Used ONLY when actually independent (one endpoint of the interpolation). -/
lemma quotient_alone [Fintype V] (t a : R.Mode) (ha : a.val ⊆ t.val) (m : Poly R)
    (hm : m.part R.quiet=1)
    (hprod : ∀ s : R.Mode, a.val ⊆ s.val → s.val ⊆ t.val →
      m.part s=m.part a * m.part (diff s a.val)) :
    quotient t.val a.val m = Poly.send a (m.part a) := by
  have hv : root t.val a.val m = Poly.send a (m.part a) * outer t.val a.val m := by
    ext j
    rw [root_part, mul_at_part]
    by_cases hj : a.val ⊆ j.val
    · have hx (h : j.val⊆t.val) : (diff j a.val).val ⊆ t.val := sdiff_subset.trans h
      have hy := (separates j a hj).1.symm
      by_cases hh : j.val ⊆ t.val
      · rw [if_pos ⟨hh,hj⟩, if_pos hj, outer_part, if_pos ⟨hx hh,hy⟩]; exact hprod j hj hh
      rw [if_neg (by simp [hh]), if_pos hj, outer_part, if_neg, mul_zero]
      intro h
      apply hh; rw [← (separates j a hj).2]; exact union_subset ha h.1
    rw [if_neg (by simp [hj]), if_neg hj]
  have hO := right_inverse (show (outer t.val a.val m).part R.quiet=1 from (outer_quiet ..).trans hm)
  rw [quotient,hv,mul_assoc,hO,mul_one]
end Anchor
end YM.Primitives.GCC
