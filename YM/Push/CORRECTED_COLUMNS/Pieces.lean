import YM.Push.CORRECTED_COLUMNS.Totals

/-!
# K on the same vacuum, and attaching h on mask cubes

Keep original label addresses *inside* unions. No nonempty path
component lost, actual footprints and inventory through reindexing.
No weakening of x roots moment arm used here. Even zero summands
on admissible label sets are handled on exactly this accounting.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected
open Set MeasureTheory Lattice Wilson RG Marker Function
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {n : Side} {G : Gauge} {V A : Type*} [DecidableEq V] [DecidableEq A] {R : Census V}
variable {P : Rep G n} {v : V → Site n}
abbrev oldSites (P : Rep G n) i := (P.activities.forced i).support
abbrev claims (P : Rep G n) i := (P.activities.forced i).inventory
abbrev permits (P : Rep G n) i := (P.activities.forced i).eligible P.p.threshold

/-- Whole polynomial at each *pre*-address; requires actual coverage,
reads on footprint, not just a scalar expression for a collapsed
cluster. -/
structure Original (P : Rep G n) (v : V → Site n) (R : Census V) where
  value : ℕ → Config G n → Poly R
  pure i U : (value i U).part R.quiet=(P.activities.K i U:ℂ)
  locality i : Width.LocalCharge P.p v (oldSites P i) (value i)
  keeps (i U) : value i U≠0 → permits P i U

/-- One per head. Activated only at a failed mask. -/
structure AddedHeads (P : Rep G n) (v : V → Site n) (R : Census V) (A : Type*) where
  support : A → Support n
  distinct i j : i ≠ j → Disjoint (support i) (support j)
  some i : (support i).Nonempty
  value : A → Config G n → Poly R
  hot i U : (value i U).part R.quiet=0
  locally i : Width.LocalCharge P.p v (support i) (value i)
  fails i U : Healthy P.p.threshold (support i) U → value i U=0

namespace UnionK
variable (L : Original P v R) (Q : AddedHeads P v R A)



def patch : ℕ ⊕ A → Support n := Sum.elim (oldSites P) Q.support
def unionOf (s : Finset (ℕ ⊕ A)) := s.biUnion (patch Q)
def inventory (P : Rep G n) (s : Finset (ℕ ⊕ A)) : Support n := s.toLeft.biUnion (claims P)

def value : (ℕ ⊕ A) → Config G n → Poly R := Sum.elim L.value Q.value
omit [DecidableEq A] in
lemma loc (i) : Width.LocalCharge P.p v (patch Q i) (value L Q i) := by cases i; exacts [L.locality _, Q.locally _]
omit [DecidableEq A] in
lemma present (i) : (patch Q i).Nonempty := by
  cases i with
  | inl i => exact (P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup
  | inr i => exact Q.some _

def Joining (s : Finset (ℕ ⊕ A)) := Ac.Spark (patch Q) s ∧ s.toLeft.Nonempty ∧
    (s.toLeft : Set ℕ).PairwiseDisjoint (oldSites P)
abbrev Piece := {s // Joining Q s}

variable {Q} (p : Piece Q)

omit [DecidableEq A] in
lemma rich_inv : (inventory P p.val).Nonempty := by
  obtain ⟨j,hj⟩ := p.property.2.1; obtain ⟨x,hx⟩ := (P.activities.forced j).inventory_ne
  exact ⟨x,Finset.mem_biUnion.mpr ⟨j,hj,hx⟩⟩
omit [DecidableEq A] in
lemma sized : inventory P p.val⊆unionOf Q p.val := by
  intro x hx
  obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hx; exact Finset.mem_biUnion.mpr ⟨Sum.inl i,Finset.mem_toLeft.mp hi,
    (P.activities.forced _).inventory_sup hv⟩

def actual (p : Piece Q) (U : Config G n) := unionOf Q p.val ∩ flags P.p.threshold U = inventory P p.val

omit [DecidableEq A] in
private lemma seenFlags (p : Piece Q) : MeasurableSet {U : Config G n| actual p U} := by
  let f (U : Config G n) := flags P.p.threshold U
  let B (l : Support n) := {U : Config G n| f U=l}
  rw [show {U : Config G n | actual p U}= ⋃ (j : Support n) (_ : unionOf Q p.val ∩ j = inventory P p.val),B j by
    ext x; simp only [actual,Set.mem_iUnion, Set.mem_setOf_eq, B, exists_prop]
    exact ⟨fun h => ⟨f x,h,rfl⟩, fun ⟨j,h,e⟩ => by subst j; exact h⟩]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => flags_measurable_eq ..

open scoped Classical in
def activated (L : Original P v R) (p : Piece Q) (U : Config G n) := if actual p U then ∏ i∈p.val,value L Q i U else 0

omit [DecidableEq A] in
lemma gathered : Width.LocalCharge P.p v (unionOf Q p.val) (activated L p) := by
  classical
  have he := Width.product_local (p:=P.p) p.val (value L Q) (fun i hi =>
    (loc L Q i).widen (fun x hx => Finset.mem_biUnion.mpr ⟨i,hi,hx⟩))
  constructor
  · intro θ U
    by_cases h : actual p U
    · have ht : actual p (Lattice.gauge θ U) := by unfold actual; rw [gauge_flags]; exact h
      unfold activated; rw [if_pos h,if_pos ht]; exact he.gauge ..
    have ht : ¬ actual p (Lattice.gauge θ U) := by simpa [actual] using h
    unfold activated; rw [if_neg ht,if_neg h]
  · exact Measurable.ite (seenFlags p) he.borel measurable_const
  · intro U W hx hu
    unfold activated; simp only [actual, hu]
    split
    · exact he.reads U W hx hu
    rfl
  intro U i hi w hw
  unfold activated at hi; split at hi
  · exact he.carry U i hi w hw
  simp at hi

variable (Q)

def singleton (i : ℕ) : Piece Q := ⟨{Sum.inl i}, by
  refine ⟨⟨Finset.singleton_nonempty _,fun a ha b hb => ?_⟩,?_,?_⟩
  · rw [Finset.mem_singleton.mp ha,Finset.mem_singleton.mp hb]; exact .refl
  · exact ⟨i,Finset.mem_toLeft.mpr (Finset.mem_singleton_self _)⟩
  intro a ha b hb e
  exact False.elim (e ((by simpa using Finset.mem_toLeft.mp ha : a=i).trans (show i=b by simpa [eq_comm] using Finset.mem_toLeft.mp hb)))⟩

omit [DecidableEq A] in
lemma was (i : ℕ) : unionOf Q (singleton Q i).val=oldSites P i := by simp [unionOf,singleton,patch]
omit [DecidableEq A] in
lemma still (i : ℕ) : inventory P (singleton Q i).val=claims P i := by
  unfold inventory
  rw [show (singleton Q i).val.toLeft={i} by ext; rw [Finset.mem_toLeft]; simp [singleton]]; simp
omit [DecidableEq A] in
lemma older (i U) : activated L (singleton Q i) U = L.value i U := by
  unfold activated; split
  · simp [value,singleton]
  rename_i h
  contrapose! h
  rw [actual,was,still]; exact (L.keeps i U (Ne.symm h)).1

omit [DecidableEq A] in
lemma leftover {p : Piece Q} (h : p.val.toRight=∅) : ∃ i : ℕ, p=singleton Q i := by
  obtain ⟨i,hi⟩ := p.property.2.1
  have hi' := Finset.mem_toLeft.mp hi
  refine ⟨i, Subtype.ext ?_⟩
  have hv : ∀ j∈p.val, j=Sum.inl i := by
    intro j hj
    have hw a (ha : a∈p.val) : ∃ i, a=Sum.inl i := by
      cases a with
      | inl i => exact ⟨_,rfl⟩
      | inr i => exact False.elim ((Finset.notMem_empty i) (h ▸ Finset.mem_toRight.mpr ha))
    have hx := p.property.1.2 (Sum.inl i) hi' j hj
    induction hx with
    | refl => rfl
    | @tail k j _ hh ih =>
      obtain ⟨v,hv⟩ := hw j hh.2.1
      obtain ⟨w,ht⟩ := hw k hh.1
      subst k j
      have hm := ih hh.1
      rcases eq_or_ne w v with ht|ht
      · rw [←ht]; exact hm
      obtain ⟨x,h₁,h₂⟩ := hh.2.2
      exact False.elim (Finset.disjoint_left.mp (p.property.2.2
        (Finset.mem_toLeft.mpr hh.1) (Finset.mem_toLeft.mpr hh.2.1) ht) h₁ h₂)
  ext x
  exact ⟨fun h => Finset.mem_singleton.mpr (hv _ h), fun h => (Finset.mem_singleton.mp (show x∈ ({Sum.inl i}:Finset (ℕ⊕A)) from h)) ▸ hi'⟩

omit [DecidableEq A] in
lemma onlyMarks (p : Piece Q) (h : p.val.toRight.Nonempty) (U) : (activated L p U).part R.quiet=0 := by
  unfold activated; split
  · obtain ⟨i,hi⟩ := h
    let f : Poly R →* ℂ := { toFun x := x.part R.quiet, map_mul' := Poly.quiet_mul, map_one' := by simp only [Poly.one_part, ↓reduceIte] }
    change f (∏ i∈p.val,value L Q i U)=0
    rw [map_prod]; exact Finset.prod_eq_zero (Finset.mem_toRight.mp hi) (Q.hot ..)
  exact Poly.part_nil _

-- Global old polynomial.
open scoped Classical in
def oldEval (s : Finset ℕ) (U : Config G n) := if P.activities.admissible P.p U s then ∏ i∈s,L.value i U else 0

/-- Every part reassembled at the outside. Inventory & contacts inside kept. -/
def lives (J : Finset (Piece Q)) (U : Config G n) :=
    (J:Set (Piece Q)).PairwiseDisjoint (fun p => unionOf Q p.val) ∧ J.biUnion (fun p => inventory P p.val)= flags P.p.threshold U

open scoped Classical in
def newEval (J : Finset (Piece Q)) (U : Config G n) := if lives Q J U then ∏ p∈J, activated L p U else 0
end UnionK
end YM.Push.Corrected
