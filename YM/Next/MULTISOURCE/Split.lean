import YM.Marker.Weight

/-!
# Partition calculus for mixed perturbations

`parts R`: add a formal first-order variable for *each* nonempty allowed
set of physical variables. Allow collections of these whose **substitution**
by the corresponding monomials is nonzero. This gives a square-zero
jet algebra with an algebra homomorphism back to that on the original names.
No orderings on names; no arity-dependent multiplicity on one partition.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi

open Marker Finset
open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V]

/-- Nonempty choices. A vertex of the partition calculus. -/
abbrev Hot (R : Census V) := {s : R.Mode // s.val.Nonempty}

namespace Hot

variable {R : Census V}

abbrev sites (x : Hot R) := x.val.val

def one (R : Census V) (v : V) : Hot R := ⟨R.fire v, singleton_nonempty _⟩

@[simp] lemma sites_one (v : V) : sites (one R v) = {v} := rfl

@[simp] lemma one_inj (v w : V) : one R v = one R w ↔ v = w := by
  simp [one]

lemma eq_of_sites {x y : Hot R} : sites x = sites y → x = y := fun h => Subtype.ext (Subtype.ext h)

lemma one_of_card {x : Hot R} (h : x.sites.card = 1) : ∃ v, one R v = x := by
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h
  exact ⟨a,eq_of_sites ha.symm⟩
end Hot

variable {R : Census V}

/-- Keep exactly the partitions of modes of `R`. -/
def parts (R : Census V) : Census (Hot R) where
  choices := Finset.univ.filter fun s : Finset (Hot R) =>
    (s : Set (Hot R)).Pairwise (fun i j => Disjoint i.sites j.sites) ∧ s.biUnion Hot.sites ∈ R.choices
  blank := by simp [R.blank, Set.Pairwise]
  solo i := by simp
  down := by
    intro x hx y h
    simp only [mem_filter, mem_univ, true_and] at *
    refine ⟨hx.1.mono h,R.down hx.2 _ (Finset.biUnion_subset.mpr ?_)⟩
    intro i hi j hj
    exact mem_biUnion.mpr ⟨i,h hi,hj⟩

lemma parts_wise (q : (parts R).Mode) : (q.val : Set (Hot R)).Pairwise
    (fun i j => Disjoint i.sites j.sites) := ((Finset.mem_filter.mp q.property).2).1

def unionOf (q : (parts R).Mode) : R.Mode := ⟨q.val.biUnion Hot.sites, ((Finset.mem_filter.mp q.property).2).2⟩

@[simp] lemma unionOf_empty : unionOf (parts R).quiet = R.quiet := by simp [Census.quiet, unionOf]

@[simp] lemma unionOf_single (x : Hot R) : unionOf ((parts R).fire x) = x.val := by simp [Census.fire, unionOf]

def unionOfHot (q : Hot (parts R)) : Hot R :=
  ⟨unionOf q.val, by
    obtain ⟨i,hi⟩ := q.property
    obtain ⟨j,hj⟩ := i.property
    exact ⟨j, Finset.mem_biUnion.mpr ⟨i, hi, hj⟩⟩⟩

@[simp] lemma unionOfHot_one (x : Hot R) : unionOfHot (Hot.one (parts R) x) = x :=
  Subtype.ext (unionOf_single _)

lemma merge_union {x y z : (parts R).Mode} (h : Poly.merges x y z) :
    Poly.merges (unionOf x) (unionOf y) (unionOf z) := by
  obtain ⟨hd, he⟩ := h
  unfold unionOf
  refine ⟨Finset.disjoint_left.mpr ?_,?_⟩
  · intro i hi hj
    obtain ⟨m,hm,hM⟩ := mem_biUnion.mp hi
    obtain ⟨n,hn,hN⟩ := mem_biUnion.mp hj
    have hm' : m ∈ z.val := he ▸ mem_union_left _ hm
    have hn' : n ∈ z.val := he ▸ mem_union_right _ hn
    have hne : m ≠ n := fun r => Finset.disjoint_left.mp hd (r ▸ hm) hn
    exact Finset.disjoint_left.mp (parts_wise z hm' hn' hne) hM hN
  dsimp only
  rw [← he, Finset.union_biUnion]

lemma merge_union_inv {x y : (parts R).Mode} {z : R.Mode} (h : Poly.merges (unionOf x) (unionOf y) z) :
    ∃ w, Poly.merges x y w := by
  obtain ⟨hd,he⟩ := h
  have hD (i j : Hot R) (hi : i ∈ x.val) (hj : j ∈ y.val) : Disjoint i.sites j.sites :=
    Finset.disjoint_left.mpr fun a ha hb => Finset.disjoint_left.mp hd
      (Finset.mem_biUnion.mpr ⟨i,hi,ha⟩) (Finset.mem_biUnion.mpr ⟨j,hj,hb⟩)
  have hX : x.val ∪ y.val ∈ (parts R).choices := by
    refine Finset.mem_filter.mpr ⟨mem_univ _,?_,?_⟩
    · rw [Finset.coe_union, Set.pairwise_union]
      exact ⟨parts_wise x, parts_wise y, fun i hi j hj _ => ⟨hD i j hi hj,(hD i j hi hj).symm⟩⟩
    rw [Finset.union_biUnion]; change (unionOf x).val ∪ (unionOf y).val ∈ R.choices; rw [he]; exact z.property
  refine ⟨⟨_,hX⟩,Finset.disjoint_left.mpr ?_,rfl⟩
  intro i hi hj; obtain ⟨a,ha⟩ := i.property
  exact Finset.disjoint_left.mp (hD i i hi hj) ha ha

lemma send_add (x : R.Mode) (a b : ℂ) : Poly.send x (a+b)=Poly.send x a+Poly.send x b := by
  ext i; by_cases e : i=x <;> simp [e]
lemma send_scale (x : R.Mode) (a b : ℂ) : Poly.send x (a*b)=a • Poly.send x b := by
  ext i; by_cases e : i=x <;> simp [e]

lemma send_prod {x y z : R.Mode} (h : Poly.merges x y z) (a b : ℂ) :
    Poly.send x a * Poly.send y b = Poly.send z (a*b) := by
  ext i
  change (Poly.prod _ _).part i = _
  rw [Poly.cart,Poly.part_send]
  by_cases e : i=z
  · subst i; rw [if_pos h, if_pos rfl]
  rw [if_neg e,if_neg (show ¬ Poly.merges x y i from fun k => e (Subtype.ext (k.2.symm.trans h.2)))]

lemma send_noProd {x y : R.Mode} (h : ¬ ∃ z, Poly.merges x y z) (a b : ℂ) :
    Poly.send x a * Poly.send y b = 0 := by
  ext i; change (Poly.prod _ _).part i = 0
  rw [Poly.cart,if_neg (show ¬Poly.merges x y i from fun k => h ⟨_,k⟩)]

def substituteL (R : Census V) : Poly (parts R) →ₗ[ℂ] Poly R where
  toFun a := ∑ x, Poly.send (unionOf x) (a.part x)
  map_add' a b := by simp only [Poly.part_plus, send_add, Finset.sum_add_distrib]
  map_smul' r a := by simp only [Poly.part_smul, send_scale, Finset.smul_sum, RingHom.id_apply]

lemma substituteL_send (x : (parts R).Mode) (a : ℂ) :
    substituteL R (Poly.send x a) = Poly.send (unionOf x) a := by
  unfold substituteL
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Poly.part_send]
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl]
  · intro i _ hi; simp [hi]
  simp

def substitute (R : Census V) : Poly (parts R) →ₐ[ℂ] Poly R := by
  refine AlgHom.ofLinearMap (substituteL R) ?_ ?_
  · change substituteL R (Poly.send _ _) = Poly.send _ _
    rw [substituteL_send,unionOf_empty]
  have hp (x y : (parts R).Mode) (a b : ℂ) : substituteL R (Poly.send x a * Poly.send y b) =
      substituteL R (Poly.send x a) * substituteL R (Poly.send y b) := by
    rw [substituteL_send,substituteL_send]
    by_cases h : ∃ z, Poly.merges x y z
    · obtain ⟨z,h⟩ := h
      rw [send_prod h, substituteL_send, send_prod (merge_union h)]
    rw [send_noProd h, send_noProd (x:=unionOf x) (by
      rintro ⟨w,h'⟩
      exact h (merge_union_inv h')), map_zero]
  intro x y
  rw [← Poly.studs x, ← Poly.studs y]
  simp_rw [Finset.sum_mul, Finset.mul_sum, map_sum, hp, Finset.sum_mul, Finset.mul_sum]

lemma substitute_apply (x : Poly (parts R)) : substitute R x = substituteL R x := rfl

/- `map_one` etc. fold used via explicit rw later. -/
end YM.Multi
