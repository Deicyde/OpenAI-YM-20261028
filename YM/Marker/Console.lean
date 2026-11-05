import YM.Shoot.Criteria

/-!
# Finite marker algebra

Actual commuting square-zero markers with any stipulated downward closed
exclusions and all singletons (exclude a name entirely by restricting type).
Counts on product commute, coefficients on distinct selections are **not
modulo a permutation**. Ring operations here for finite expressions in
occurrences; later budgets use explicit hit costs and no hidden norm conversion
as number of markers grows. Π-type estimates on `Poly` with sup norm only for
arguments at fixed marker set / continuity. `Coeff.T` read at single marker
later via `fire`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Marker
open Function Finset
open scoped BigOperators Topology ENNReal

variable {V : Type*} [DecidableEq V]
structure Census (V : Type*) [DecidableEq V] where
  choices : Finset (Finset V)
  blank : ∅ ∈ choices
  solo i : {i} ∈ choices
  down : ∀ {x}, x∈choices → ∀ y ⊆ x, y∈choices

namespace Census
variable (R : Census V)
abbrev Mode := ↥R.choices
def quiet : R.Mode := ⟨∅,R.blank⟩
def fire (v : V) : R.Mode := ⟨{v},R.solo v⟩
@[simp] lemma fire_inj (v w : V) : R.fire v=R.fire w ↔ v=w := by simp [fire]
lemma fire_hot (v : V) : R.fire v ≠ R.quiet := by simp [fire,quiet]
end Census

variable {R : Census V}

-- type synonym hide pointwise multiplication instance.
def Poly (R : Census V) := R.Mode → ℂ
namespace Poly
def part (f : Poly R) : R.Mode → ℂ := f
def inject (f : R.Mode → ℂ) : Poly R := f

instance : AddCommGroup (Poly R) := inferInstanceAs (AddCommGroup (R.Mode → ℂ))
instance : Module ℂ (Poly R) := inferInstanceAs (Module ℂ (R.Mode → ℂ))

@[ext] theorem ext {f g : Poly R} (h : ∀ v, part f v=part g v) : f=g := funext h

/-- from scalar & tag. -/
def send (x : R.Mode) (v : ℂ) := inject (Pi.single x v)

@[simp] lemma part_plus (f g : Poly R) (x : R.Mode) : (f+g).part x= f.part x+g.part x := rfl
@[simp] lemma part_nil (x : R.Mode) : (0 : Poly R).part x=0 := rfl
@[simp] lemma part_neg (f : Poly R) (x : R.Mode) : (-f).part x= -f.part x := rfl
@[simp] lemma part_smul (r : ℂ) (f : Poly R) (x : R.Mode) : (r • f).part x=r*f.part x := rfl
@[simp] lemma part_send (x y : R.Mode) (v : ℂ) : (send x v).part y=if y=x then v else 0 := Pi.single_apply _ _ _
@[simp] lemma send_zero (x : R.Mode) : send x 0=0 := by ext i; simp

/-- predicate used BEFORE evaluation to combine. -/
def merges (x y z : R.Mode) := Disjoint x.val y.val ∧ x.val∪ y.val=z.val
instance (x y z : R.Mode) : Decidable (merges x y z) := by unfold merges; infer_instance

lemma wind (x y z : R.Mode) : merges x y z ↔ merges y x z := by unfold merges; rw [union_comm,disjoint_comm]

@[simp] lemma vacuum (a b : R.Mode) : merges R.quiet a b ↔ a=b := by rw [merges]; simp only [Census.quiet, empty_union,Finset.disjoint_empty_left,true_and]; exact Subtype.ext_iff.symm

def prod (p q : Poly R) : Poly R := inject fun z => ∑ x, ∑ y, if merges x y z then part p x*part q y else 0

lemma product (p q : Poly R) (x : R.Mode) : (prod p q).part x=∑ i, ∑ j, if merges i j x then p.part i*q.part j else 0 := rfl

lemma prod_commutative (a b : Poly R) : prod a b=prod b a := by
  ext u; change (∑ x, ∑ y, if merges x y u then _ else _)=∑ x, ∑ y, if merges x y u then _ else _
  rw [sum_comm]; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by simp only [wind j i u]; split <;> simp [mul_comm]

lemma on_left (a b c : Poly R) : prod (a+b) c=prod a c+prod b c := by
  ext i
  simp only [part_plus,product]
  rw [← sum_add_distrib]; refine sum_congr rfl fun j _ => ?_
  rw [← sum_add_distrib]; refine sum_congr rfl fun k _ => ?_
  split <;> simp [*,add_mul]

lemma on_vac (a : Poly R) : prod (send R.quiet 1) a=a := by
  ext i; rw [product, sum_eq_single R.quiet]
  · simp
  · intro b _ hb; simp [hb]
  simp

lemma no_one (a : Poly R) : prod a 0=0 := by
  ext i
  suffices ∑ x, ∑ y, (if merges x y i then a.part x*(0 : Poly R).part y else 0)=0 from this
  simp

lemma part_sum {M} (S : Finset M) (f : M → Poly R) (x : R.Mode) : (∑ i∈S,f i).part x=∑ i∈S,(f i).part x := by
  let g : Poly R →+ ℂ := { toFun := fun b => b.part x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum g ..

lemma studs (b : Poly R) : (∑ i,send i (b.part i))=b := by ext; simp [part_sum]

lemma cart (x y z : R.Mode) (i j : ℂ) : (prod (send x i) (send y j)).part z=
    if merges x y z then i*j else 0 := by
  change (∑ a : R.Mode, ∑ b : R.Mode, if merges a b z then (send x i).part a*(send y j).part b else 0)=_
  rw [sum_eq_single x]
  · rw [sum_eq_single y]; simp
    · intro b _ hb; simp [hb]
    simp
  · intro b _ hb; simp [hb]
  simp

lemma atom_left (a b c d : R.Mode) (i j k : ℂ) :
    (prod (prod (send a i) (send b j)) (send c k)).part d=
      if ∃ x, merges a b x ∧ merges x c d then i*j*k else 0 := by
  change (∑ x, ∑ y, if merges x y d then (prod _ _).part x * (send c k).part y else 0)=_
  split_ifs with h
  · obtain ⟨x,hx,h⟩ := h
    rw [sum_eq_single x, sum_eq_single c]; simp only [if_pos h,cart, if_pos hx,part_send,↓reduceIte]
    · intro b _ hb; simp [hb]
    · simp
    · intro y _ hy
      have ht : ¬ merges a b y := fun H => hy (Subtype.ext (H.2.symm.trans hx.2))
      simp [cart,ht]
    simp
  refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
  by_cases hh : y=c
  · subst y
    rw [cart]; split_ifs with he hz; exact False.elim (h ⟨_,hz,he⟩)
    all_goals simp
  simp [hh]

lemma three (x y z i : R.Mode) : (∃ a, merges x y a ∧ merges a z i) ↔ ∃ b, merges y z b ∧ merges b x i := by
  have hh (a b c : R.Mode) : (∃ j, merges a b j ∧ merges j c i) → ∃ k, merges b c k ∧ merges k a i := by
    rintro ⟨j,⟨he,h⟩,⟨hr,ha⟩⟩
    rw [← h] at *
    simp only [disjoint_union_left] at hr
    exact ⟨⟨_,R.down i.property (b.val∪c.val) (by rw [← ha,union_assoc]; exact Finset.subset_union_right)⟩,
      ⟨hr.2,rfl⟩,⟨disjoint_union_left.mpr ⟨he.symm,hr.1.symm⟩,by dsimp only; rw [← ha]; simp [union_comm,union_left_comm]⟩⟩
  exact ⟨hh x y z, (hh z x y) ∘ (hh y z x)⟩

lemma atom_assoc (a b c : R.Mode) (i j k) : prod (prod (send a i) (send b j)) (send c k)=prod (send a i) (prod (send b j) (send c k)) := by
  rw [prod_commutative (send a i) (prod (send b j) (send c k))]; ext x; simp only [atom_left,three a b c]; split <;> ac_rfl

lemma prod_sum {M} (S : Finset M) (X : M → Poly R) (a : Poly R) : prod (∑ i∈S,X i) a=∑ i∈S,prod (X i) a := by
  let B : Poly R →+ Poly R := { toFun := fun i => prod i a, map_zero' := prod_commutative _ a |>.trans (no_one a), map_add' := fun x y => on_left x y a }
  exact map_sum B ..
lemma prod_sum' {M} (a : Poly R) (S : Finset M) (X : M → Poly R) : prod a (∑ i∈S,X i)=∑ i∈S,prod a (X i) := by
  rw [prod_commutative a, prod_sum]; exact sum_congr rfl fun i _ => prod_commutative (X i) a

instance : CommRing (Poly R) :=
  { (inferInstance : AddCommGroup (Poly R)) with
    mul := prod
    one := send R.quiet 1
    mul_comm := prod_commutative
    mul_one := fun a => (prod_commutative ..).trans (on_vac a)
    one_mul := on_vac
    right_distrib := on_left
    left_distrib := fun a b c => by change prod a (b+c)=prod a b+prod a c; simp_rw [prod_commutative a, on_left]
    mul_assoc := fun a b c => by
      change prod (prod a b) c=prod a (prod b c)
      rw [← studs a,← studs b, ← studs c]
      simp_rw [prod_sum,prod_sum',prod_sum,atom_assoc]
      exact sum_congr rfl fun i _ => Finset.sum_comm
    zero_mul := fun a => (prod_commutative ..).trans (no_one a)
    mul_zero := no_one }
end Poly
end YM.Marker
