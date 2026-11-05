import YM.Ac.Nodes
import YM.RG.Activities

set_option warningAsError false

/-!
# Back and forth on the complete declared footprints

This file is structural.

Give it actual tested output
supports, NOT numerical function supports.

Think one address for each compulsory packet (covers
all its seed halos), one for each optional *variant* (retains the parent physical address), one
for each selected K (support incl projections and queried flag reads).

Work on subsets (Γ copies
for log handled later, don't run these lemmas on a flattened multiset!).

Assembly sees negative and
dormant answers too; use `Retained` even on the eligibility tests themselves.

No claims here of
achieving the `Retained` or partition/protector hypotheses nor that records meeting these graph
conditions give good prices under the measure.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect

open Lattice Filter Function RG

variable {c : Side} {ι : Type*} [DecidableEq ι]

namespace Words

/-- Occupied complete footprint of a selection of addresses. -/
abbrev region (X : ι → Support c) (s : Finset ι) : Support c := s.biUnion X
/-- Not indexed by the supports but by address sets — many component data may be on the same halo. -/
def Apart (X : ι → Support c) (b : Finset (Finset ι)) : Prop :=
    (b : Set (Finset ι)).PairwiseDisjoint (region X)

def Pieces (X : ι → Support c) (b : Finset (Finset ι)) : Prop :=
    Apart X b ∧ ∀ p∈b, Ac.Spark X p

lemma partition (X : ι → Support c) (s : Finset ι) : Pieces X (Ac.Parts X s) :=
  ⟨Ac.separate .., fun _ h => (Ac.lives X s h).2⟩

/-- Genuine equivalence of layouts, not of their nonzero terms only. -/
def assemble (X : ι → Support c) : {b // Pieces X b} ≃ Finset ι where
  toFun b := b.val.biUnion id
  invFun s := ⟨Ac.Parts X s, partition X s⟩
  left_inv := by
    rintro ⟨b,hb⟩; exact Subtype.ext (Ac.separates X b hb.2 hb.1)
  right_inv := Ac.reconstruct X

omit [DecidableEq ι] in
lemma region_sub {X : ι → Support c} {p s : Finset ι} (h : p ⊆ s) : region X p ⊆ region X s := by
  intro x hx; obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨i,h hi,he⟩

lemma owner {X : ι → Support c} {p s : Finset ι} (hp : p ∈ Ac.Parts X s)
    {i j} (hi : i ∈ p) (hj : j∈s) (h : ¬Disjoint (X i) (X j)) : j∈p := by
  have hconn : Ac.chain X s i j := .single ⟨(Ac.lives X s hp).1 hi,hj,Finset.not_disjoint_iff.mp h⟩
  rw [← Ac.contains X hp _ hi]
  exact (Ac.bright X i j).mpr ⟨hj,hconn⟩

lemma owner' {X : ι → Support c} {p s : Finset ι} (hp : p∈Ac.Parts X s)
    {j} (hj : j∈s) (h : ¬Disjoint (region X p) (X j)) : j∈p := by
  obtain ⟨x,hx,hy⟩ := Finset.not_disjoint_iff.mp h
  obtain ⟨i,hi,hi'⟩ := Finset.mem_biUnion.mp hx
  exact owner hp hi hj (Finset.not_disjoint_iff.mpr ⟨x,hi',hy⟩)

omit [DecidableEq ι] in
lemma no_duplicate (X : ι → Support c) (hX : ∀ i,(X i).Nonempty) {b : Finset (Finset ι)}
    (h : Apart X b) : (b : Set (Finset ι)).PairwiseDisjoint id := by
  intro p hp q hq hn
  refine Finset.disjoint_left.mpr ?_
  intro i hi hj
  obtain ⟨x,hx⟩:=hX i
  exact Finset.disjoint_left.mp (h hp hq hn)
    (Finset.mem_biUnion.mpr ⟨i,hi,hx⟩) (Finset.mem_biUnion.mpr ⟨i,hj,hx⟩)

lemma after_union (D : ι → Support c) (b : Finset (Finset ι)) :
    region D (b.biUnion id) = b.biUnion (region D) := by
  ext
  simp only [region, Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨i,⟨p,hp,hi⟩,hv⟩; exact ⟨p,hp,i,hi,hv⟩
  · rintro ⟨p,hp,i,hi,hv⟩; exact ⟨i,⟨p,hp,hi⟩,hv⟩

lemma parts_union (X : ι → Support c) (D : ι → Support c) (s : Finset ι) :
    (Ac.Parts X s).biUnion (region D) = region D s := by
  rw [← after_union, Ac.reconstruct]

omit [DecidableEq ι] in
lemma region_inventory {X D : ι → Support c} (hD : ∀ i,D i ⊆ X i) (p : Finset ι) :
    region D p ⊆ region X p := by
  intro i hi
  obtain ⟨j,hj,hv⟩:=Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨j,hj,hD j hv⟩

omit [DecidableEq ι] in
/-- The one-time final flag test can be inserted on assembled gas families even at unforced
components: coverage and *support* disjointness, not merely disjoint inventories. -/
lemma readable {X D : ι → Support c} (hD : ∀ i,D i⊆X i) {b : Finset (Finset ι)}
    (h : Apart X b) {S : Support c} (he : b.biUnion (region D) = S) (p : Finset ι) (hp : p∈b) :
    region X p ∩ S = region D p := by
  ext x
  rw [← he,Finset.mem_inter]
  constructor
  · rintro ⟨hx,ht⟩; obtain ⟨q,hq,hy⟩:=Finset.mem_biUnion.mp ht
    by_cases H : p=q
    · exact H.symm ▸ hy
    · exact (Finset.disjoint_left.mp (h hp hq H) hx (region_inventory hD q hy)).elim
  intro hx
  exact ⟨region_inventory hD p hx, Finset.mem_biUnion.mpr ⟨_,hp,hx⟩⟩

lemma read_partition {X D : ι → Support c} (hD : ∀ i,D i ⊆ X i) {S : Support c} {s : Finset ι}
    (he : region D s = S) (p : Finset ι) (hp : p∈Ac.Parts X s) : region X p ∩ S = region D p :=
  readable hD (partition X s).1 ((parts_union X D s).trans he) p hp

/-! ## Local table lookups -/

/-- Locality of an address/table rule in the *choices*, including off branches. `Y i` is all
queried positions at address i, `X` the complete dependency support of every possible address
including addresses changing those answers. Can usually take Y = X. -/
def Within {α : Sort*} (X : ι → Support c) (Y : Support c) (F : Finset ι → α) :=
    ∀ s b, (∀ j, ¬Disjoint Y (X j) → (j ∈ s ↔ j∈ b)) → F s = F b

def Retained {α : Sort*} (X : ι → Support c) (F : ι → Finset ι → α) := ∀ i,Within X (X i) (F i)

lemma unchanged {X : ι → Support c} {p s : Finset ι} (hp : p ∈ Ac.Parts X s) {α : Sort*}
    {Y : Support c} {F : Finset ι → α} (hF : Within X Y F) (hY : Y ⊆ region X p) : F s = F p := by
  apply hF; intro j hj
  exact ⟨fun he => owner' hp he (fun hv => hj (Finset.disjoint_of_subset_left hY hv)), fun hh => (Ac.lives X s hp).1 hh⟩

lemma restrict_table {X : ι → Support c} {p s : Finset ι} (hp : p ∈ Ac.Parts X s) {α : Sort*}
    {F : ι → Finset ι → α} (hF : Retained X F) {i : ι} (hi : i∈p) : F i s = F i p :=
  unchanged hp (hF i) (fun _ he => Finset.mem_biUnion.mpr ⟨i,hi,he⟩)

/-- Form a selection lookup table by recording every selected address hitting queried
positions (a test using only a subset of the committed footprints also works). In particular
this needn't index over global *candidate* configurations of table contents. -/
def lookup (X : ι → Support c) (Y : Support c) (s : Finset ι) := s.filter fun i =>
    decide (¬ Disjoint Y (X i))

omit [DecidableEq ι] in
lemma via_table (X : ι → Support c) (Y : Support c) : Within X Y (lookup X Y) := by
  intro s b he; ext; simp only [lookup,Finset.mem_filter, decide_eq_true_eq]; exact and_congr_left (he _)

/-- Check a (possibly many-answer) address table with a function using the literal selected
list at positions it can query. Include negative answers. -/
def permits (E : ι → Finset ι → Prop) (s : Finset ι) := ∀ i∈s,E i s

lemma eligible_parts {E : ι → Finset ι → Prop} {X : ι → Support c} (h : Retained X E) (s : Finset ι) :
    permits E s ↔ ∀ p∈Ac.Parts X s, permits E p := by
  constructor
  · intro hp p hh i hi
    exact (restrict_table hh h hi) ▸ hp i ((Ac.lives X s hh).1 hi)
  intro hh i hi
  let p := Ac.burst X s i
  have hp : p ∈ Ac.Parts X s := Finset.mem_image_of_mem _ hi
  have ht : i ∈ p := (Ac.bright X _ _).mpr ⟨hi,.refl⟩
  rw [restrict_table hp h ht]
  exact hh _ hp i ht

omit [DecidableEq ι] in
/-- Example of proving Retained from complete-support data: enforcing parent-address
exclusions once, e.g. alternative marks at an optional h (all variants read at least one of
the same physical sites regardless of whether their numerical coefficient is used) or packet
conflict or old K-overlap prohibition. -/
lemma ret_excludes {X : ι → Support c} (banned : ι → ι → Prop) (h : ∀ i j,banned i j →
    ¬Disjoint (X i) (X j)) : Retained X (fun i s => ∀ j∈s, i ≠ j → ¬banned i j) := by
  intro i s b he
  refine propext ⟨fun H j hj hn hv => H j ((he j (h _ _ hv)).2 hj) hn hv,
    fun H j hj hn hv => H j ((he j (h _ _ hv)).1 hj) hn hv⟩

omit [DecidableEq ι] in
/-- Similarly *requiring* an incidence for each selected address, without choosing a unique
paying seed. -/
lemma ret_needs {X : ι → Support c} (needs : ι → ι → Prop) (h : ∀ i j,needs i j →
    ¬Disjoint (X i) (X j)) : Retained X (fun i s => ∃ j∈s,needs i j) := by
  intro i s b he
  refine propext ?_; constructor
  · rintro ⟨j,hj,H⟩; exact ⟨j,(he _ (h _ _ H)).1 hj,H⟩
  · rintro ⟨j,hj,H⟩; exact ⟨j,(he _ (h _ _ H)).2 hj,H⟩

omit [DecidableEq ι] in
lemma ret_all {δ : Sort*} {X : ι → Support c} {E : δ → ι → Finset ι → Prop}
    (h : ∀ d,Retained X (E d)) : Retained X (fun i s => ∀ d,E d i s) := by
  intro i s b he
  refine propext (forall_congr' (fun d => ?_))
  rw [h d i s b he]

/-! ## Conditional exact merging on infinite series -/

variable {W : Type*} [AddCommMonoid W] [TopologicalSpace W]

lemma reindex {X : ι → Support c} {g : Finset ι → W} {f : Finset (Finset ι) → W} {a : W}
    (hz : ∀ b, ¬Pieces X b → f b = 0) (he : ∀ s,f (Ac.Parts X s) = g s) :
    HasSum g a ↔ HasSum f a := by
  have hX (s : Finset ι) : f ((assemble X).symm s).val = g s := he s
  have hR : HasSum g a ↔ HasSum (f ∘ (Subtype.val : {b : Finset (Finset ι) // Pieces X b} → _)) a := by
    rw [← (assemble X).symm.hasSum_iff]; simp only [Function.comp_def, hX]
  refine hR.trans ?_
  convert! hasSum_subtype_iff_of_support_subset (s := {b | Pieces X b}) (f := f) ?_ using 1
  intro b hb; exact of_not_not (fun hn => hb (hz b hn))

section gas

open scoped Classical

/-- gas already including final-read indicator. Spark eligibility (distinct placements,
incidences with compulsory packets etc) also inside coefficient. Local coefficient `u` used
before these final tests. Invalid/nonconnected components can stay on alphabet as zeros. -/
def clause (E : ι → Finset ι → Prop) (X D : ι → Support c) (S : Support c)
    (u : Finset ι → ℝ) (p : Finset ι) := if permits E p ∧ region X p ∩ S = region D p then u p else 0

def openOccurrence (X D : ι → Support c) (S : Support c) (u : Finset ι → ℝ) (b : Finset (Finset ι)) :=
    if Pieces X b ∧ b.biUnion (region D) = S then ∏ i∈b,u i else 0

/-- Reconstruction of all layouts. Input G from actual terms of an expanded formula or their
integrals; need only on-sector factorizability, don't infer it from this graph. Every appearance
of E, D must be from ONE list of addresses. -/
theorem layout_sum {E : ι → Finset ι → Prop} {X D : ι → Support c} (hE : Retained X E)
    (hD : ∀ i,D i ⊆ X i) (S : Support c) (G u : Finset ι → ℝ)
    (he : ∀ s, permits E s → region D s = S → G s = ∏ i∈Ac.Parts X s, u i) (b : ℝ) :
    HasSum (fun s => if permits E s ∧ region D s = S then G s else 0) b ↔
      HasSum (openOccurrence X D S (clause E X D S u)) b := by
  apply reindex (X:=X) (fun b hb => by simp [openOccurrence,hb]); intro s
  have ht := parts_union X D s
  by_cases hn : region D s = S
  · simp only [openOccurrence, partition,ht,hn, ↓reduceIte, and_true]
    by_cases hm : permits E s
    · rw [if_pos hm,he _ hm hn]
      refine Finset.prod_congr rfl fun i hi => ?_
      exact if_pos ⟨(eligible_parts hE s).1 hm _ hi, read_partition hD hn _ hi⟩
    rw [if_neg hm]
    rw [eligible_parts hE] at hm
    push Not at hm
    obtain ⟨p,hp,hq⟩:=hm
    apply Finset.prod_eq_zero hp
    simp [clause,hq]
  simp [openOccurrence,ht,hn]
end gas
end Words
end YM.SectorNext.Reconnect
