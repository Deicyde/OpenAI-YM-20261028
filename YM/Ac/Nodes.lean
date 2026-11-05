import YM.Lattice.Support
/-!
# address recovery

external flag-read convention. `X` is the FULL tested
footprint of the letter (not inferred by value-equivalence).
Graph reindexing only, asserts no compatibility of payload formulas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ac
open Relation Lattice  Finset
variable {ι : Type*} [DecidableEq ι] {n : Side} (X : ι → Support n)

def meets (i : ι) (D : Support n) := ∃ x∈D,x∈X i
abbrev bonds (s : Finset ι) := fun i j => i∈s ∧ j∈s ∧ meets X j (X i)
def chain (s : Finset ι) (i j : ι) := ReflTransGen (bonds X s) i j
def Pack (Y : Support n) (s : Finset ι) := ∀ i∈s,∃ j∈s, meets X j Y ∧ chain X s j i
open scoped Classical in
def burst (s : Finset ι) (i : ι) := s.filter (chain X s i)

omit [DecidableEq ι] in
lemma swaps {s : Finset ι} {i j} (h : chain X s i j) : chain X s j i := by
  induction h with
  | refl => exact .refl
  | tail _ HH ih =>
    obtain ⟨h1,h2,x,h3,h4⟩ := HH
    exact .head ⟨h2,h1,x,h4,h3⟩ ih

omit [DecidableEq ι] in
lemma bright {s : Finset ι} (i j : ι) : j∈ burst X s i ↔ j∈s ∧ chain X s i j := by
  classical
  simp [burst]

omit [DecidableEq ι] in
lemma same {s : Finset ι} {i j : ι} (h : chain X s i j) : burst X s i=burst X s j := by
  ext k; rw [bright,bright]; exact and_congr_right fun _ =>
    ⟨fun hh => ReflTransGen.trans (swaps X h) hh,fun hh => ReflTransGen.trans h hh⟩

omit [DecidableEq ι] in
lemma glows {s : Finset ι} {i j : ι} (hj : j∈burst X s i) : chain X (burst X s i) i j := by
  induction (bright X _ _).mp hj |>.2 with
  | refl => exact .refl
  | @tail k j h HH ih =>
    have hk : k∈burst X s i := (bright X _ _).mpr ⟨HH.1,h⟩
    exact .tail (ih hk) ⟨hk,hj,HH.2.2⟩

/-- nonempty connected word -/
def Spark (s : Finset ι) := s.Nonempty ∧ ∀ i∈s,∀ j∈s,chain X s i j

omit [DecidableEq ι] in
lemma burning (s : Finset ι) (i : ι) (hi : i∈s) : Spark X (burst X s i) :=
  ⟨⟨i,(bright X _ _).mpr ⟨hi,.refl⟩⟩,fun _ hj _ hk => ReflTransGen.trans (swaps X (glows X hj)) (glows X hk)⟩

abbrev Parts (s : Finset ι) := s.image (burst X s)
lemma lives (s : Finset ι) {p : Finset ι} (hp : p∈Parts X s) : p⊆ s ∧ Spark X p := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
  exact ⟨fun k hk => ((bright X _ _).mp hk).1,burning X s i hi⟩

lemma reconstruct (s : Finset ι) : (Parts X s).biUnion id=s := by
  ext i; constructor
  · intro h; obtain ⟨p,hp,h⟩ := mem_biUnion.mp h; exact (lives X s hp).1 h
  intro h; exact mem_biUnion.mpr ⟨_,mem_image_of_mem _ h, (bright X _ _).mpr ⟨h,.refl⟩⟩

lemma contains {s : Finset ι} {p : Finset ι} (hp : p∈Parts X s) (i : ι) (hi : i∈p) : burst X s i=p := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hp; exact (same X ((bright X _ _).mp hi).2).symm

lemma different (s : Finset ι) : (Parts X s : Set (Finset ι)).PairwiseDisjoint id := by
  intro p hp q hq hn
  exact disjoint_left.mpr fun i hi hj => hn ((contains X hp i hi).symm.trans (contains X hq i hj))

lemma separate (s : Finset ι) : ((Parts X s:Finset (Finset ι)) : Set (Finset ι)).PairwiseDisjoint (fun p => p.biUnion X) := by
  intro p hp q hq h
  apply disjoint_left.mpr; intro x hx he
  obtain ⟨i,h1,h2⟩ := mem_biUnion.mp hx; obtain ⟨j,h3,h4⟩ := mem_biUnion.mp he
  have hr : chain X s i j := .single ⟨(lives X s hp).1 h1,(lives X s hq).1 h3,x,h2,h4⟩
  exact h ((contains X hp i h1).symm.trans ((same X hr).trans (contains X hq j h3)))

lemma separates (s : Finset (Finset ι)) (hw : ∀ i∈s,Spark X i)
    (ht : (s:Set (Finset ι)).PairwiseDisjoint (fun p => p.biUnion X)) : Parts X (s.biUnion id)=s := by
  let q := s.biUnion id
  have hq {p} (hp : p∈s) : p ⊆ q := fun i hi => mem_biUnion.mpr ⟨p,hp,hi⟩
  have he {p} (hp : p∈s) {i} (hi : i∈p) : burst X q i=p := by
    have hr (j) (hj : chain X q i j) : j∈p := by
      induction hj with
      | refl => exact hi
      | @tail k j _ hb IH =>
        obtain ⟨h1,h2,x,h3,h4⟩ := hb
        obtain ⟨D,hD,hd⟩ := mem_biUnion.mp h2
        by_cases h : p=D
        · exact h.symm ▸ hd
        exact False.elim ((disjoint_left.mp (ht hp hD h)) (mem_biUnion.mpr ⟨k,IH,h3⟩) (mem_biUnion.mpr ⟨j,hd,h4⟩))
    ext j; rw [bright]; constructor
    · rintro ⟨-,hz⟩; exact hr _ hz
    intro hx
    exact ⟨hq hp hx, ReflTransGen.mono (p:= bonds X q) (fun a b (hb : bonds X p a b) =>
      ⟨hq hp hb.1,hq hp hb.2.1,hb.2.2⟩) _ _ ((hw _ hp).2 _ hi _ hx)⟩
  ext p; rw [Parts, mem_image]; constructor
  · rintro ⟨i,hi,rfl⟩; obtain ⟨D,hD,hz⟩ := mem_biUnion.mp hi; change burst X q i∈s; rw [he hD hz]; exact hD
  intro hp; obtain ⟨i,h⟩ := (hw p hp).1
  exact ⟨i,hq hp h,he hp h⟩

lemma excise {s : Finset ι} {i} (h : Spark X s) (hi : i∈s) : Pack X (X i) (s.erase i) := by
  intro j hj
  have hh : j ≠ i := ne_of_mem_erase hj
  induction (h.2 _ hi _ (mem_of_mem_erase hj)) with
  | refl => contradiction
  | @tail k j _ hv ih =>
    by_cases H : k=i
    · subst k; exact ⟨j,hj,hv.2.2,.refl⟩
    have hk := mem_erase.mpr ⟨H,hv.1⟩
    obtain ⟨l,h1,h2,h3⟩ := ih hk H
    exact ⟨l,h1,h2,.tail h3 ⟨hk,hj,hv.2.2⟩⟩

lemma packHits {s : Finset ι} {Y} (h : Pack X Y s) (p) (hp : p∈Parts X s) : ∃ i∈p, meets X i Y := by
  obtain ⟨i,h1,rfl⟩ := mem_image.mp hp
  obtain ⟨j,h2,h3,h4⟩ := h i h1
  exact ⟨j,(bright X _ _).mpr ⟨h2,swaps X h4⟩,h3⟩
end YM.Ac
