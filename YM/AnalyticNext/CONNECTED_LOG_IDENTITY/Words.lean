import YM.Push.ABSOLUTE_SUMS.Breadth


set_option warningAsError false

/-!
Reindexing. Complete query/variable footprints on ONE periodic output
lattice. In particular, this geometry needn't be the previous K
hard-core geometry (that exclusion can still be tested *internally*).
Alphabet is of addresses, incl variants/histories; selecting two
variants of one parent in the same spelling, or failing an incidence,
can also be excluded internally. A letter is selected only once;
occurrence repeats e.g. in a restoration exponential can be kept as
*decorations*, not counted as distinct components.

Separate module(s) for when and how the word costs themselves FACTOR,
required for use, and for the Ursell and restoration operations. Also,
as usual use tsum results with summability checks (API here both for
exact identities and for summability).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity

open Lattice RG Finset Function
open scoped Classical BigOperators Topology

variable {n : Side} {ι : Type*}

/-- Hard disjointness in the specified geometry, Finset (unordered DISTINCT addresses). -/
def Apart (X : ι → Support n) (s : Finset ι) := (s : Set ι).PairwiseDisjoint X

/-- Geometry and exact global coverage check. For inventories `I i ⊆ X i`
the union equality here with Apart is also disjoint-union equality. -/
def Records (X I : ι → Support n) (D : Support n) (s : Finset ι) :=
  Apart X s ∧ s.biUnion I = D

/-- One term of a gas with inventories. Raw term weights, predicate failures
(e.g. a K is not eligible at this V) can already be zeros in w. -/
def gasTerm (X I : ι → Support n) (D : Support n) (w : ι → ℝ) (s : Finset ι) :=
  if Records X I D s then ∏ i∈s, w i else 0

lemma inventories {X I : ι → Support n} (hI : ∀ i, I i ⊆ X i) {s : Finset ι}
    {D : Support n} (hr : Records X I D s) {i : ι} (hi : i ∈ s) :
    X i ∩ D = I i := by
  ext x; rw [mem_inter]
  constructor
  · rintro ⟨hx, he⟩
    rw [← hr.2] at he
    obtain ⟨j,hj,h⟩ := mem_biUnion.mp he
    by_cases hh : i = j
    · simpa [hh] using h
    exact False.elim (Finset.disjoint_left.mp (hr.1 hi hj hh) hx (hI j h))
  intro h
  refine ⟨hI i h, ?_⟩
  rw [← hr.2]; exact mem_biUnion.mpr ⟨i,hi,h⟩

lemma gasTerm_stamp (X I : ι → Support n) (D : Support n) (w : ι → ℝ) (s : Finset ι)
    (hI : ∀ i, I i ⊆ X i) :
    gasTerm X I D w s = gasTerm X I D (fun i => if X i ∩ D = I i then w i else 0) s := by
  unfold gasTerm
  split
  next h => exact prod_congr rfl fun i hi => (if_pos (inventories hI h hi)).symm
  next h => rfl

section Geometry
variable (X : ι → Support n)

/-- Integrated species addresses, before V-dependent checks. -/
abbrev Species := {s : Finset ι // Ac.Spark X s}

def ground (p : Species X) := p.val.biUnion X

def owned (I : ι → Support n) (p : Species X) := p.val.biUnion I

lemma species_ground {i : ι} {p : Species X} (hi : i∈p.val) : X i ⊆ ground X p :=
  fun _ h => mem_biUnion.mpr ⟨i,hi,h⟩



lemma owned_ground (I : ι → Support n) (hI : ∀ i,I i⊆X i) (p : Species X) :
    owned X I p ⊆ ground X p := by
  intro x h; obtain ⟨i,hi,h⟩ := mem_biUnion.mp h
  exact species_ground X hi (hI i h)

private def bindParts (s : Finset ι) (p : ↥(Ac.Parts X s)) : Species X :=
  ⟨p.val,(Ac.lives X _ p.property).2⟩

def explode (s : Finset ι) : Finset (Species X) :=
  (Ac.Parts X s).attach.image (bindParts X s)

lemma exploded {s : Finset ι} (p : Species X) : p ∈ explode X s ↔ p.val ∈ Ac.Parts X s := by
  rw [explode,mem_image]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact i.property
  intro h
  exact ⟨⟨p.val,h⟩,mem_attach ..,Subtype.ext rfl⟩

def collect (t : Finset (Species X)) := t.biUnion Subtype.val

def plain (t : Finset (Species X)) : Finset (Finset ι) := t.image Subtype.val



lemma plain_inj : Injective (plain X) := Finset.image_injective Subtype.val_injective

lemma collect_plain (t : Finset (Species X)) : collect X t = (plain X t).biUnion id := by
  ext x; simp [collect,plain]

lemma plain_explode (s : Finset ι) : plain X (explode X s) = Ac.Parts X s := by
  ext p; rw [plain,mem_image]
  constructor
  · rintro ⟨q,hq,rfl⟩; exact (exploded X q).mp hq
  intro h; exact ⟨⟨p,(Ac.lives X s h).2⟩,(exploded X _).mpr h,rfl⟩

lemma collect_explode (s : Finset ι) : collect X (explode X s) = s := by
  rw [collect_plain,plain_explode,Ac.reconstruct]

lemma apart_explode (s : Finset ι) : Apart (ground X) (explode X s) := by
  intro i hi j hj hn
  change Disjoint (i.val.biUnion X) (j.val.biUnion X)
  exact Ac.separate X s ((exploded X _).mp hi) ((exploded X _).mp hj)
    (fun h => hn (Subtype.ext h))

/-- Disjoint components reconstruct the original spelling. No multiplicity
factor for ordering these components. -/
theorem explode_collect (t : Finset (Species X)) (h : Apart (ground X) t) :
    explode X (collect X t) = t := by
  apply plain_inj X
  rw [plain_explode,collect_plain]
  apply Ac.separates X
  · intro p hp; obtain ⟨p,he,rfl⟩ := mem_image.mp hp; exact p.property
  intro p hp q hq hn
  obtain ⟨p,hp2,rfl⟩ := mem_image.mp hp
  obtain ⟨q,hq2,rfl⟩ := mem_image.mp hq
  exact h hp2 hq2 (fun he => hn (congr_arg Subtype.val he))

lemma explode_inj : Injective (explode X) := fun i j h => by rw [←collect_explode X i,h,collect_explode]

lemma explode_range (t : Finset (Species X)) : t ∈ Set.range (explode X) ↔ Apart (ground X) t := by
  constructor
  · rintro ⟨p,rfl⟩; exact apart_explode X p
  intro h; exact ⟨_,explode_collect X t h⟩

lemma collect_incl {t : Finset (Species X)} {p : Species X} (h : p ∈ t) : p.val ⊆ collect X t :=
  fun _ e => mem_biUnion.mpr ⟨p,h,e⟩

lemma collect_owned (I : ι → Support n) (t : Finset (Species X)) :
    (collect X t).biUnion I = t.biUnion (owned X I) := by
  ext x
  simp only [collect,owned,mem_biUnion]
  constructor
  · rintro ⟨i,⟨p,hp,hi⟩,hx⟩; exact ⟨p,hp,i,hi,hx⟩
  rintro ⟨p,hp,i,hi,hx⟩; exact ⟨i,⟨p,hp,hi⟩,hx⟩

lemma explode_owned (I : ι → Support n) (s : Finset ι) :
    (explode X s).biUnion (owned X I) = s.biUnion I := by rw [← collect_owned,collect_explode]

lemma explode_blocks (s : Finset ι) : (explode X s : Set (Species X)).PairwiseDisjoint Subtype.val := by
  intro i hi j hj hn
  exact Ac.different X s ((exploded X _).mp hi) ((exploded X _).mp hj)
    (fun h => hn (Subtype.ext h))



/-- All factors, including query addresses whose answer stays the same.
`view` even passes the caller if self-overlapping. Local tables or masks
that ignore parts of the view are allowed. -/
def view (s : Finset ι) (i : ι) := s.filter fun j => ¬ Disjoint (X i) (X j)

lemma view_mem (s : Finset ι) (i j : ι) : j∈view X s i ↔ j∈s ∧ ¬ Disjoint (X i) (X j) :=
  mem_filter

lemma letter_reads (s : Finset ι) (p : Species X) (h : p∈explode X s) {i : ι} (hi : i∈p.val) :
    view X p.val i = view X s i := by
  ext j; rw [view_mem,view_mem]
  have hh := (exploded X _).mp h
  have hp := (Ac.lives X _ hh).1
  constructor
  · exact And.imp (fun hj => hp hj) id
  rintro ⟨hj,he⟩
  refine ⟨?_,he⟩
  rw [← Ac.contains X hh i hi]
  obtain ⟨x,hx,hX⟩ := Finset.not_disjoint_iff.mp he
  exact (Ac.bright X _ _).mpr ⟨hj,.single ⟨hp hi,hj,x,hx,hX⟩⟩

def internal (test : ι → Finset ι → Prop) (s : Finset ι) :=
  ∀ i∈s, test i (view X s i)

lemma internal_iff (s : Finset ι) (test : ι → Finset ι → Prop) :
    internal X test s ↔ ∀ p∈explode X s, internal X test p.val := by
  constructor
  · intro h p hp i hi
    rw [letter_reads X s p hp hi]; exact h i ((Ac.lives X _ ((exploded X _).mp hp)).1 hi)
  intro h i hi
  have H := hi; rw [← collect_explode X s] at H
  obtain ⟨p,hp,hI⟩ := mem_biUnion.mp H
  rw [← letter_reads X s p hp hI]; exact h _ hp _ hI

lemma per_parts {M : Type*} [CommMonoid M] (s : Finset ι) (w : ι → M) :
    ∏ i∈s,w i = ∏ p∈explode X s, ∏ i∈p.val,w i := by
  rw [← Finset.prod_biUnion (explode_blocks X s)]
  change _ = ∏ i∈collect X (explode X s), w i
  rw [collect_explode]

lemma per_component {M : Type*} [CommMonoid M] (s : Finset ι) (w : ι → Finset ι → M) :
    ∏ i∈s,w i (view X s i) = ∏ p∈explode X s, ∏ i∈p.val,w i (view X p.val i) := by
  rw [per_parts X s]
  apply prod_congr rfl; intro p hp
  apply prod_congr rfl; intro i hi
  rw [letter_reads X s p hp hi]

end Geometry

section Reorder
variable (X I : ι → Support n) (D : Support n)

/-- Evaluation use: u is the value of ONE spell before the compatibility
and exact inventory checks (but may already use internal eligibility).
Specify the component/marginal factorization `hf` separately. -/
theorem term_reindex (u : Finset ι → ℝ) (w : Species X → ℝ)
    (hf : ∀ s : Finset ι, s.biUnion I = D → u s = ∏ p∈explode X s, w p) (s : Finset ι) :
    (if s.biUnion I = D then u s else 0) = gasTerm (ground X) (owned X I) D w (explode X s) := by
  simp only [gasTerm,Records,apart_explode,explode_owned,true_and]
  split
  next h => exact hf _ h
  next h => rfl

lemma term_outside (w : Species X → ℝ) {t : Finset (Species X)} (h : t ∉ Set.range (explode X)) :
    gasTerm (ground X) (owned X I) D w t = 0 := if_neg (fun he => h ((explode_range X _).mpr he.1))

/-- Use only with absolute hypotheses proved (also see below). -/
lemma first (u : Finset ι → ℝ) (w : Species X → ℝ)
    (hf : ∀ s : Finset ι, s.biUnion I = D → u s = ∏ p∈explode X s, w p) :
    (∑' s : Finset ι, if s.biUnion I = D then u s else 0) = ∑' t, gasTerm (ground X) (owned X I) D w t := by
  have he : Function.support (gasTerm (ground X) (owned X I) D w) ⊆ Set.range (explode X) := by
    intro t ht; by_contra hh; exact ht (term_outside X I D w hh)
  rw [← (explode_inj X).tsum_eq he]; exact tsum_congr (term_reindex X I D u w hf)



end Reorder
end YM.Push.LogIdentity
