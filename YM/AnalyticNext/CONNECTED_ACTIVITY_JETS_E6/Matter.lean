import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood

/-!
# Which bodies occur. α' EXACT safety bits and incidence
Use same alphabet, duplicates disallowed. Merge all Stores. Layout
ignores unused sectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Matter
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {Z Z' : Support c}
variable {k k' : Finset ℕ} {w v : Air f G} {L : Side} {X : Coat T F}
variable {V : Finset (Molecule S)} {b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}

-- independent H.
def areas (R : Rep G f) (T : Tube G S) (l B : ℕ) := Mixed.foot S l B (footprints T R l B)
def ground (R : Rep G f) (T : Tube G S) (l B : ℕ) (p : Molecule S) := p.biUnion (areas R T l B)

def own (p : Molecule S) := p.toRight.toLeft

def roster (p : Molecule S) : Stores S := Packets.store S (p.toLeft.biUnion (seeds S))

def troupe (_T : Tube G S) (R : Rep G f) (d B : ℕ) (p : Molecule S) :=
    Layout (roster p) d B p.toLeft ∧ Contract.sealed R (own p) ∧ Contract.incidence R (own p) (roster p)

/-- For the emission test (at actual V). -/
def covers (X : Coat T F) (V : Finset (Molecule S)) := V.biUnion (fun Q=> (roster Q).flags)= RG.flags (Pressure.temp X.x) X.V

def claimed (X : Coat T F) (R : Rep G f) (l : ℕ) (p : Molecule S) := troupe T R l X.B p ∧
    RG.flags (Pressure.temp X.x) X.V∩ground R T l X.B p=(roster p).flags

def standsIn (X : Coat T F) (R : Rep G f) (l : ℕ) (p : Molecule S) := Ac.Spark (areas R T l X.B) p ∧ claimed X R l p

def joints (T : Tube G S) (R : Rep G f) (d b : ℕ) (V : Finset (Molecule S)) :=
    (∀ i∈ V, Ac.Spark (areas R T d b) i) ∧ (V:Set (Molecule S)).PairwiseDisjoint (ground R T d b)

lemma branches {X : Stores S} (Y : Molecule S) (h : Layout X l b Y.toLeft) : roster Y=X := by
  unfold roster; rw [← h.every, Packets.store_seeds]
lemma register (p : Molecule S) : Packets.seeds S (roster p)=p.toLeft.biUnion (Packets.seeds S) := Packets.seeds_store ..
lemma subparts (i j : Molecule S) (h : i⊆j) : i.toLeft⊆j.toLeft := fun _ hx=> mem_toLeft.mpr (h <| mem_toLeft.mp hx)
lemma subrows (i j : Molecule S) (h : i⊆j) : own i⊆own j := fun _ hx=> mem_toLeft.mpr (mem_toRight.mpr (h <| mem_toRight.mp (mem_toLeft.mp hx)))

lemma star_sizes (V : Finset (Molecule S)) (a : Seed S) : a∈ Packets.seeds S (roster (V.biUnion id)) ↔
    ∃ i∈V,a∈Packets.seeds S (roster i) := by
  simp only [register,mem_biUnion,mem_toLeft,id_eq]; grind
lemma literal (p : Molecule S) (i : ℕ) : i∈own p ↔ Sum.inr (Sum.inl i)∈p := by simp [own]
lemma gloss (V : Finset (Molecule S)) (i : ℕ) : i∈own (V.biUnion id) ↔ ∃ p∈V,i∈own p := by simp [own,mem_biUnion]
lemma claim_zoneK (R : Rep G f) (T : Tube G S) (l b : ℕ) (i : Molecule S) {y : Site f} (j : ℕ) (hj : j∈own i)
    (hf : y∈(R.activities.forced j).support) : S.ratio.parent y∈ground R T l b i := by
  apply mem_biUnion.mpr; refine ⟨_,(literal i j).1 hj, ?_⟩
  exact halo_subset _ _ (mem_image_of_mem _ (show y∈RG.inspected (R.activities.forced j).support from mem_union_left _ hf))
lemma claim_zoneA (R : Rep G f) (T : Tube G S) (l b : ℕ) (i : Molecule S) (p : Seed S) (he : p∈Packets.seeds S (roster i)) :
    Packets.points S p⊆ground R T l b i := by
  intro z hz; rw [register] at he; obtain ⟨x,hx,he⟩ := mem_biUnion.mp he
  refine mem_biUnion.mpr ⟨Sum.inl x,mem_toLeft.mp hx,?_⟩; exact halo_subset (l*b) x.place
    (show z∈x.place from Packets.place_reads S x ▸ mem_biUnion.mpr ⟨p,he,hz⟩)
lemma range (p : Molecule S) : (roster p).place⊆ground R T l b p := by
  rw [← place_reads]; intro z hz; obtain ⟨j,hj,hz⟩ := mem_biUnion.mp hz; exact claim_zoneA R T l b p j hj hz
lemma range_flags (p : Molecule S) : (roster p).flags⊆ground R T l b p := fun _ hi=> Matter.range _ (mem_union_right _ hi)
lemma totals (V : Finset (Molecule S)) : (roster (V.biUnion id)).flags=V.biUnion fun i=> (roster i).flags := by
  ext i; simpa only [Packets.seeds,inr_mem_disjSum,mem_biUnion] using star_sizes V (Sum.inr (Sum.inr i))
lemma separates (h : joints T R d b V) : Ac.Parts (areas R T d b) (V.biUnion id)=V := Ac.separates _ _ h.1 h.2
lemma unweave (h : joints T R d b V) : (V:Set (Molecule S)).PairwiseDisjoint id :=
    by have hv := separates h; have hp := Ac.different (areas R T d b) (V.biUnion id); rwa [hv] at hp

namespace Propels
variable (h : joints T R d b V)

/- Disjoint scheduling theorem; seeds and K compatible iff locally. -/
include h in
theorem climates : troupe T R d b (V.biUnion id) ↔ ∀ i∈V,troupe T R d b i := by
  let Λ := V.biUnion id
  have hz : Λ.toLeft= V.biUnion fun i=> i.toLeft := by ext i; simp [Λ,mem_biUnion]
  have hx i (hi : i∈V) : i⊆Λ := subset_biUnion_of_mem id hi
  let f p:=ground R T d b p
  have hk p e (ht : e∈ (p:Molecule S).toLeft) : e.dome (d*b)⊆f p := subset_biUnion_of_mem (areas R T d b) (mem_toLeft.mp ht)
  have he p q (hj : p∈V) (hk : q∈V) (i) (hp : i∈f p) (hq : i∈f q) : p=q := by
    by_contra hn; exact Finset.disjoint_left.mp (h.2 hj hk hn) hp hq
  have hC p j : j∈ (roster p).costs ↔ Sum.inl j∈Packets.seeds S (roster p) := by simp [Packets.seeds]
  change troupe T R d b Λ ↔ _
  constructor
  · rintro ⟨hY,hA,H⟩ i hi
    refine ⟨⟨fun j hj=> hY.checkpoints j ((subparts i Λ (hx _ hi)) hj),
      hY.crews.subset (subparts i Λ (hx _ hi)), register _⟩, fun _ hv _ hh => hA (subrows i Λ (hx _ hi) hv) (subrows i Λ (hx _ hi) hh),?_⟩
    intro p hp j hj
    obtain ⟨x,hq,hb⟩ := H p ((subrows i Λ (hx _ hi)) hp) j hj
    obtain ⟨v,hv,hq⟩ := (star_sizes V _).1 ((hC _ _).1 hq)
    have hh := he v i hv hi (S.ratio.parent j) (claim_zoneA R T _ _ v _ hq (mem_image_of_mem _ hb))
      (claim_zoneK R T _ _ i _ hp ((R.activities.forced p).inventory_sup hj))
    exact ⟨x,(hC _ _).2 (hh ▸ hq),hb⟩
  intro H
  refine ⟨⟨?_,?_,register Λ⟩,?_,?_⟩
  · rw [hz]; intro i hp; obtain ⟨v,hv,hp⟩ := mem_biUnion.mp hp; exact (H v hv).1.checkpoints i hp
  · rw [hz]; intro i hi j hj hZ
    obtain ⟨p,hp,hi⟩ := mem_biUnion.mp hi; obtain ⟨q,hq,hj⟩ := mem_biUnion.mp hj
    by_cases ht : p=q
    · subst q; exact (H p hp).1.crews hi hj hZ
    exact ((h.2 hp hq ht).mono_left (hk p i hi)).mono_right (hk q j hj)
  · intro i hi j hj ht
    obtain ⟨p,hp,hi⟩ := (gloss V _).1 hi; obtain ⟨q,hq,hj⟩ := (gloss V _).1 hj
    by_cases hV : p=q
    · subst q; exact (H p hp).2.1 hi hj ht
    exact Finset.disjoint_left.mpr fun y hy hw=> hV (he p q hp hq (S.ratio.parent y)
      (claim_zoneK R T _ _ p i hi hy) (claim_zoneK R T _ _ q j hj hw))
  intro i hi y hy; obtain ⟨p,hp,hi⟩ := (gloss V _).1 hi
  obtain ⟨j,hj,hh⟩ := (H p hp).2.2 i hi y hy
  exact ⟨j,(hC _ _).2 ((star_sizes V _).2 ⟨p,hp,(hC _ _).1 hj⟩),hh⟩

end Propels
end YM.ConnectedActivityE6.Matter
