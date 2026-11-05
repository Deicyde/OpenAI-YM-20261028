import YM.Ac.Nodes
import YM.Next.MULTISOURCE.Packs


/-!
# Merger for marked complements into the actual forced vacuum

Retain the old `Pack`s. Connected components of this overlap graph, not a
product of single conditional expectations. Budgets charged on unions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Couples
open RG Wilson Lattice Finset Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {n : Side} {V : Type} [DecidableEq V] [Fintype V] (Y : V → Support n)

abbrev Atom (n : Side) (V : Type) := Pack n ⊕ V
abbrev Recipe (n : Side) (V : Type) := Finset (Atom n V)

def span : Atom n V → Support n := Sum.elim Pack.zone Y

def ground (b : Recipe n V) := b.biUnion (span Y)
def tags (b : Recipe n V) := b.toLeft.biUnion Pack.flagsAt

omit [DecidableEq V] [Fintype V] in
def fused (b : Recipe n V) : Pack n := by
  by_cases h : b.toLeft.Nonempty
  · refine ⟨⟨ground Y b,tags b⟩, ?_,?_⟩
    · obtain ⟨x,hx⟩ := h
      obtain ⟨i,hi⟩ := x.property.1
      exact ⟨i,mem_biUnion.mpr ⟨x,hx,hi⟩⟩
    intro i hi; obtain ⟨p,hp,hi⟩ := mem_biUnion.mp hi
    exact mem_biUnion.mpr ⟨Sum.inl p, mem_toLeft.mp hp,p.property.2 hi⟩
  exact ⟨⟨{0},{0}⟩,singleton_nonempty _,le_rfl⟩

def boxes := Finset.univ.filter fun b : Recipe n V =>
    b.toLeft.Nonempty ∧ (b.toLeft : Set (Pack n)).PairwiseDisjoint Pack.zone ∧ Ac.Spark (span Y) b

omit [DecidableEq V] in
lemma owns (b) : b∈boxes Y ↔
    b.toLeft.Nonempty ∧ (b.toLeft : Set (Pack n)).PairwiseDisjoint Pack.zone ∧ Ac.Spark (span Y) b := by
  simp [boxes]

omit [DecidableEq V] in
lemma fused_eq {b} (h : b∈boxes Y) : (fused Y b).val = (ground Y b,tags b) := by
  simp only [fused, dif_pos ((owns ..).mp h).1]

omit [DecidableEq V] in
lemma merged_zone {b} (h : b∈boxes Y) : (fused Y b).zone=ground Y b := by simp only [Pack.zone, fused_eq Y h]
omit [DecidableEq V] in
lemma merged_tags {b} (h : b∈boxes Y) : (fused Y b).flagsAt=tags b := by simp only [Pack.flagsAt, fused_eq Y h]

/-- Output selection test for entries compressed by `fused`. -/
def accepted (D : Support n) := (boxes Y).powerset.filter fun B : Finset (Recipe n V) =>
    B.image (fused Y) ∈ Pack.clears D ∧ Set.InjOn (fused Y) B

/-- Input selection includes gathering condition (funded later by complement triggers) -/
def intake (D : Support n) := univ.filter fun s : Recipe n V =>
    s.toLeft∈ Pack.clears D ∧ Ac.Parts (span Y) s ⊆ boxes Y

omit [DecidableEq V] [Fintype V] in
lemma normal (B : Finset (Recipe n V)) : B.biUnion tags=tags (B.biUnion id) := by
  ext i; constructor
  · intro hi; obtain ⟨a,ha,h⟩ := mem_biUnion.mp hi; obtain ⟨b,hb,h⟩ := mem_biUnion.mp h
    refine mem_biUnion.mpr ⟨b,mem_toLeft.mpr (mem_biUnion.mpr ⟨a,ha,mem_toLeft.mp hb⟩), h⟩
  intro hi; obtain ⟨b,hb,h⟩ := mem_biUnion.mp hi
  obtain ⟨a,ha,h'⟩ := mem_biUnion.mp (mem_toLeft.mp hb)
  exact mem_biUnion.mpr ⟨a,ha,mem_biUnion.mpr ⟨b,mem_toLeft.mpr h', h⟩⟩

omit [DecidableEq V] in
lemma criteria (B : Finset (Recipe n V)) (D : Support n) : B∈accepted Y D ↔
    B ⊆ boxes Y ∧ (B:Set (Recipe n V)).PairwiseDisjoint (ground Y) ∧ tags (B.biUnion id)=D := by
  simp only [accepted,mem_filter,mem_powerset,Pack.clears,mem_univ,true_and]
  constructor
  · rintro ⟨hb',⟨hh,he⟩,hi⟩
    refine ⟨hb',fun x hx y hy hn => ?_,?_⟩
    · change Disjoint (ground Y _) (ground Y _)
      rw [← merged_zone Y (hb' hx), ← merged_zone Y (hb' hy)]
      exact hh (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) (fun he => hn (hi hx hy he))
    rw [← normal, ← he, image_biUnion]; exact biUnion_congr rfl fun i hi => (merged_tags Y (hb' hi)).symm
  rintro ⟨hb,hd,H⟩
  refine ⟨hb,⟨?_,?_⟩,?_⟩
  · intro i hi j hj hn
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hj
    change Disjoint (fused Y x).zone (fused Y y).zone
    rw [merged_zone Y (hb hx),merged_zone Y (hb hy)]
    exact hd hx hy (fun he => hn (he ▸ rfl))
  · rw [← H, ← normal,image_biUnion]; exact biUnion_congr rfl fun i hi => merged_tags Y (hb hi)
  intro x hx y hy e
  by_contra hh
  have hE := hd hx hy hh
  change Disjoint (ground Y x) (ground Y y) at hE
  rw [← merged_zone Y (hb hx),← merged_zone Y (hb hy),e] at hE
  obtain ⟨i,hi⟩ := (fused Y y).property.1
  exact Finset.disjoint_left.mp hE ((fused Y y).property.2 hi) ((fused Y y).property.2 hi)

omit [DecidableEq V] in
lemma splits {u : Support n} (B : Finset (Recipe n V)) (h : B∈accepted Y u) :
    Ac.Parts (span Y) (B.biUnion id)=B := by
  obtain ⟨hb,h,-⟩ := (criteria ..).1 h
  exact Ac.separates (span Y) B (fun i hi => ((owns ..).1 (hb hi)).2.2) h

omit [DecidableEq V] in
lemma choose_parts {D : Support n} {b : Recipe n V} (h : b∈intake Y D) : Ac.Parts (span Y) b∈ accepted Y D := by
  obtain ⟨hi,H⟩ := (mem_filter.mp h).2
  exact (criteria ..).mpr ⟨H, Ac.separate (span Y) b, by rw [Ac.reconstruct]; exact ((mem_filter.mp hi).2).2⟩

omit [DecidableEq V] in
lemma choose_fuse {D : Support n} {B : Finset (Recipe n V)} (h : B ∈ accepted Y D) : B.biUnion id ∈ intake Y D := by
  have h₁ := splits Y B h; obtain ⟨hb,h,H⟩ := (criteria ..).mp h
  simp only [intake,mem_filter,Pack.clears,mem_univ,true_and]
  refine ⟨⟨?_, H⟩, (by rw [h₁]; exact hb)⟩
  intro i hi j hj hn
  obtain ⟨p,hp,hP⟩ := mem_biUnion.mp (mem_toLeft.mp hi)
  obtain ⟨q,hq,hQ⟩ := mem_biUnion.mp (mem_toLeft.mp hj)
  by_cases e : p=q
  · rw [← e] at hQ
    apply ((owns ..).mp (hb hp)).2.1 _ _ hn
    · exact (show i ∈ p.toLeft from mem_toLeft.mpr hP)
    exact (show j ∈ p.toLeft from mem_toLeft.mpr hQ)
  change Disjoint i.zone j.zone
  exact Finset.disjoint_left.mpr fun y hy hc => Finset.disjoint_left.mp (h hp hq e)
    (mem_biUnion.mpr ⟨Sum.inl i,hP,hy⟩) (mem_biUnion.mpr ⟨Sum.inl j,hQ,hc⟩)

omit [DecidableEq V] in
lemma inventory_at (B : Finset (Recipe n V)) {D : Support n} (h : B∈accepted Y D) {v : Recipe n V} (hv : v∈B) :
    (ground Y v) ∩ D=tags v := by
  obtain ⟨hI,hd,H⟩ := (criteria ..).mp h
  have he (v) (hv : v∈B) : tags v ⊆ ground Y v := by
    rw [← merged_zone Y (hI hv), ← merged_tags Y (hI hv)]; exact (fused Y v).property.2
  rw [← normal] at H
  rw [← H]; apply le_antisymm
  · intro i hi; obtain ⟨h,h₁⟩ := mem_inter.mp hi; obtain ⟨u,hu,hU⟩ := mem_biUnion.mp h₁
    by_cases e : u=v
    · exact e ▸ hU
    exact False.elim (Finset.disjoint_left.mp (hd hu hv e) (he u hu hU) h)
  exact fun i hi => mem_inter.mpr ⟨he _ hv hi,mem_biUnion.mpr ⟨v,hv,hi⟩⟩
end YM.Multi.Couples
