import YM.Extra.SOURCE_HISTORIES.Pencil
import YM.Next.BOUNDARY.Alias

/-!
# Gathering the birth cluster 

One coefficient uses exactly the old forced labels whose supports **meet Y**
(no expansion during this gathering). Preserve all K factors and their tests
and the actual global coverage. A receipt about available addresses on the
HISTORY is needed: do not overwrite a vacuum label to enlarge its support.
Here use a common shelf of distinct dummy labels, of the given shapes.

These lemmas are level-generic. Application to chosen path is in `Birth`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {n : Side} {G : Gauge}

/-- A countable permanent preallocation (independently of whether the
source coefficient vanishes). -/
abbrev StockTag (n : Side) := {s : Support n × Support n // s.2.Nonempty ∧ s.2 ⊆ s.1}

structure Shelf (A : Activities G n) where
  name : StockTag n × ℕ ↪ ℕ
  support t : (A.forced (name t)).support = t.1.val.1
  inventory t : (A.forced (name t)).inventory = t.1.val.2
  check t U : (A.forced (name t)).extraTest U
  blank t : A.K (name t) = 0

namespace Attach
variable (R : Rep G n) (Y : Support n)

abbrev X (i : ℕ) := (R.activities.forced i).support
abbrev I (i : ℕ) := (R.activities.forced i).inventory

abbrev coherent (b : Finset ℕ) := (b:Set ℕ).Pairwise fun i j => Disjoint (X R i) (X R j)

/-- incoming profile split by the actual incompatibility test (supports),
not by the sites of the flags. -/
def meet (b : Finset ℕ) := b.filter fun i => ¬ Disjoint (X R i) Y
def rest (b : Finset ℕ) := b.filter fun i => Disjoint (X R i) Y

lemma mem_meet (b : Finset ℕ) (i : ℕ) : i ∈ meet R Y b ↔ i ∈ b ∧ ¬ Disjoint (X R i) Y := Finset.mem_filter
lemma mem_rest (b : Finset ℕ) (i : ℕ) : i ∈ rest R Y b ↔ i ∈ b ∧ Disjoint (X R i) Y := Finset.mem_filter
lemma pieces (b) : meet R Y b ∪ rest R Y b = b := by
  ext i; simp only [Finset.mem_union,mem_meet,mem_rest]; tauto

abbrev Cluster := {b : Finset ℕ // b.Nonempty ∧ coherent R b ∧ ∀ i ∈ b, ¬ Disjoint (X R i) Y}

def span (c : Cluster R Y) := Y ∪ c.val.biUnion (X R)

def debts (c : Cluster R Y) := c.val.biUnion (I R)

lemma owns (c : Cluster R Y) (i) (hi : i ∈ c.val) : X R i ⊆ span R Y c :=
  fun _ hx => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,hx⟩)
lemma base (c : Cluster R Y) : Y ⊆ span R Y c := Finset.subset_union_left

def shape (c : Cluster R Y) : StockTag n := ⟨(span R Y c, debts R Y c),
  (by obtain ⟨i, hi⟩ := c.property.1
      obtain ⟨j,hj⟩ := (R.activities.forced i).inventory_ne
      exact ⟨j,Finset.mem_biUnion.mpr ⟨i,hi,hj⟩⟩),
  (by intro i hi
      obtain ⟨j,hj,h⟩ := Finset.mem_biUnion.mp hi
      exact owns R Y c j hj ((R.activities.forced j).inventory_sup h))⟩

variable (H : Shelf R.activities) (docket : ℕ)

def codeId (c : Cluster R Y) : StockTag n × ℕ :=
  (shape R Y c, Encodable.encode (docket,c.val))

def stamp : Cluster R Y ↪ ℕ where
  toFun c := H.name (codeId R Y docket c)
  inj' := by
    intro c c' h
    have ht := congr_arg Prod.snd (H.name.injective h)
    exact Subtype.ext (congr_arg Prod.snd (Encodable.encode_injective ht))

lemma stamp_x (c : Cluster R Y) : X R (stamp R Y H docket c) = span R Y c := H.support _
lemma stamp_i (c : Cluster R Y) : I R (stamp R Y H docket c) = debts R Y c := H.inventory _

variable (U : Config G n)

/-- Exact coverage and exclusions give inventory predicate already, even
if K on some address happens to vanish. -/
lemma seated {b : Finset ℕ} (hb : R.activities.admissible R.p U b) {i} (hi : i ∈ b) :
    X R i ∩ flags R.p.threshold U = I R i := by
  rw [← hb.2]
  ext x
  rw [Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro ⟨ht,j,hj,hk⟩
    rcases eq_or_ne i j with H|H
    · subst j; exact hk
    exact (Finset.disjoint_left.mp (hb.1 hi hj H) ht ((R.activities.forced j).inventory_sup hk)).elim
  intro hx; exact ⟨(R.activities.forced i).inventory_sup hx,i,hi,hx⟩

abbrev Old := {b : Finset ℕ // R.activities.admissible R.p U b ∧ (meet R Y b).Nonempty}
abbrev Issued := {p : Cluster R Y × Finset ℕ //
  stamp R Y H docket p.1 ∈ p.2 ∧ R.activities.admissible R.p U p.2}

def interest (b : Old R Y U) : Cluster R Y := ⟨meet R Y b.val, b.property.2,
  b.property.1.1.mono (Finset.coe_subset.mpr (Finset.filter_subset ..)), fun _ hi => ((mem_meet ..).mp hi).2⟩

private lemma aside (b : Old R Y U) {i} (hi : i∈rest R Y b.val) :
    Disjoint (X R (stamp R Y H docket (interest R Y U b))) (X R i) := by
  rw [stamp_x]
  obtain ⟨he,hx⟩ := (mem_rest ..).mp hi
  apply Finset.disjoint_left.mpr
  intro x hu hX
  obtain hd|hd := Finset.mem_union.mp hu
  · exact Finset.disjoint_left.mp hx hX hd
  obtain ⟨j, hj, hw⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hf,hq⟩ := (mem_meet ..).mp (show j ∈ meet R Y b.val from hj)
  have hc : j ≠ i := fun h => hq (h.symm ▸ hx)
  exact Finset.disjoint_left.mp (b.property.1.1 hf he hc) hw hX

private lemma stamp_notMem (b : Old R Y U) :
    stamp R Y H docket (interest R Y U b) ∉ rest R Y b.val := by
  intro ha
  have he := aside R Y H docket U b ha
  obtain ⟨x,hx⟩ := (R.activities.forced _).inventory_ne.mono
    ((R.activities.forced (stamp R Y H docket (interest R Y U b))).inventory_sup)
  exact Finset.disjoint_left.mp he hx hx

def issue (b : Old R Y U) : Issued R Y H docket U :=
  let c := interest R Y U b
  let i := stamp R Y H docket c
  ⟨(c,insert i (rest R Y b.val)),Finset.mem_insert_self ..,by
    constructor
    · rw [Finset.coe_insert]
      apply Set.Pairwise.insert (b.property.1.1.mono (Finset.coe_subset.mpr (Finset.filter_subset ..)))
      intro y hy _; have he := aside R Y H docket U b hy; exact ⟨he,he.symm⟩
    · change (insert i (rest R Y b.val)).biUnion (I R)=_
      rw [Finset.biUnion_insert, show I R i = debts R Y c from stamp_i ..]
      rw [show debts R Y c = (meet R Y b.val).biUnion (I R) from rfl, ← Finset.union_biUnion,
        pieces, show b.val.biUnion (I R) = _ from b.property.1.2]⟩

def unchanged (p : Issued R Y H docket U) := p.val.2.erase (stamp R Y H docket p.val.1)

private theorem recovers (p : Issued R Y H docket U) :
    insert (stamp R Y H docket p.val.1) (unchanged R Y H docket U p)= p.val.2 := Finset.insert_erase p.property.1

lemma far (p : Issued R Y H docket U) {i} (hi : i ∈ unchanged R Y H docket U p) :
    Disjoint (X R i) (span R Y p.val.1) :=
  stamp_x R Y H docket p.val.1 ▸ p.property.2.1 (Finset.mem_of_mem_erase hi)
    p.property.1 (Finset.ne_of_mem_erase hi)

lemma separate (p : Issued R Y H docket U) : Disjoint p.val.1.val (unchanged R Y H docket U p) := by
  apply Finset.disjoint_left.mpr; intro i hi ha
  have hx := far R Y H docket U p ha
  obtain ⟨x,hx'⟩ := (R.activities.forced _).inventory_ne.mono (R.activities.forced i).inventory_sup
  exact Finset.disjoint_left.mp hx hx' (owns _ _ _ _ hi hx')

def flatten (p : Issued R Y H docket U) : Finset ℕ := p.val.1.val ∪ unchanged R Y H docket U p

lemma meetFlatten (p : Issued R Y H docket U) : meet R Y (flatten R Y H docket U p) = p.val.1.val := by
  ext i
  rw [mem_meet]
  constructor
  · rintro ⟨hi,hb⟩
    obtain ha|hx := Finset.mem_union.mp hi
    · exact ha
    exact (hb (Finset.disjoint_of_subset_right (base ..) (far R Y H docket U p hx))).elim
  intro hi
  exact ⟨Finset.mem_union_left _ hi,p.val.1.property.2.2 i hi⟩

lemma restFlatten (p : Issued R Y H docket U) : rest R Y (flatten R Y H docket U p) = unchanged R Y H docket U p := by
  ext i
  rw [mem_rest]
  constructor
  · rintro ⟨hi,hb⟩
    obtain ha|hx := Finset.mem_union.mp hi
    · exact (p.val.1.property.2.2 i ha hb).elim
    exact hx
  intro hi
  exact ⟨Finset.mem_union_right _ hi, Finset.disjoint_of_subset_right (base ..) (far R Y H docket U p hi)⟩

def redeem (p : Issued R Y H docket U) : Old R Y U := by
  refine ⟨flatten R Y H docket U p, ⟨?_,?_⟩, meetFlatten R Y H docket U p |>.symm ▸ p.val.1.property.1⟩
  · rw [flatten,Finset.coe_union,Set.pairwise_union]
    refine ⟨p.val.1.property.2.1,p.property.2.1.mono (Finset.coe_subset.mpr (Finset.erase_subset ..)),?_⟩
    intro i hi j hj _
    have h := Finset.disjoint_of_subset_right (owns _ _ _ _ hi) (far R Y H docket U p hj)
    exact ⟨h.symm,h⟩
  change (flatten R Y H docket U p).biUnion (I R)=_
  rw [flatten,Finset.union_biUnion, show p.val.1.val.biUnion (I R)= I R (stamp R Y H docket p.val.1) from (stamp_i ..).symm,
    ← Finset.biUnion_insert, recovers, show p.val.2.biUnion (I R)=_ from p.property.2.2]

lemma unchanged_issue (b : Old R Y U) : unchanged R Y H docket U (issue R Y H docket U b) = rest R Y b.val := by
  simp only [unchanged,issue, Finset.erase_insert (stamp_notMem R Y H docket U b)]

/-- Bijection BEFORE summation. Works on all cover/exclusion-admissible
terms even those with vanishing K. -/
def routes : Old R Y U ≃ Issued R Y H docket U where
  toFun := issue R Y H docket U
  invFun := redeem R Y H docket U
  left_inv b := by
    apply Subtype.ext
    change (issue R Y H docket U b).val.1.val ∪ unchanged .. = _
    rw [unchanged_issue]; exact pieces R Y _
  right_inv p := by
    apply Subtype.ext
    have he : interest R Y U (redeem R Y H docket U p)=p.val.1 := Subtype.ext (meetFlatten ..)
    apply Prod.ext
    · exact he
    change insert (stamp R Y H docket (interest R Y U _)) (rest R Y (flatten ..)) = _
    rw [he,restFlatten]; exact recovers R Y H docket U p

end Attach
end YM.Extra.Histories
