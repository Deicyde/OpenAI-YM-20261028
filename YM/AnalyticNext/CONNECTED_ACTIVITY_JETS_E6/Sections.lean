import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Batch

/-!
# Mandatory block layout

No rebooking: Pack's Y coherence. Components can overlap e.g. Born
paths; compulsory block-block already uniquely coupled. Layout existence
actual Seeds. Σ can be empty. Inclusion and reserves at seats.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A : Stores S} {l B d : ℕ} {Y : Finset (Stores S)}

structure Layout (A : Stores S) (l B : ℕ) (X : Finset (Stores S)) : Prop where
  checkpoints : ∀ i∈X, Packets.connected S l B i
  crews : (X:Set (Stores S)).PairwiseDisjoint (fun i => i.dome (l*B))
  every : seeds S A=X.biUnion (seeds S)

namespace Layout

def rolls (A : Stores S) (l B : ℕ) := (Ac.Parts (skin S l B) (seeds S A)).image (store S)
lemma enlists (A : Stores S) (l B : ℕ) : Layout A l B (rolls A l B) := by
  let Y := rolls A l B; let X := Ac.Parts (skin S l B) (seeds S A)
  have he : Y.image (seeds S)=X := by
    change (X.image (store S)).image (seeds S)=X; rw [image_image]
    rw [show seeds S ∘ store S=id from funext fun i=> Packets.seeds_store .., image_id]
  constructor
  · rintro i hi; have hp : seeds S i∈X := he ▸ Finset.mem_image_of_mem _ hi; exact (Ac.lives _ _ hp).2
  · intro i hi j hj hn; change Disjoint (i.dome (l*B)) (j.dome (l*B)); rw [← support_reads,← support_reads]; apply Ac.separate
    · change seeds S i∈X; rw [← he]; exact mem_image_of_mem _ hi
    · change seeds S j∈X; rw [← he]; exact mem_image_of_mem _ hj
    exact (sectorAlphabet S).injective.ne hn
  change seeds S A=Y.biUnion _
  calc
    _ = X.biUnion id := (Ac.reconstruct ..).symm
    _ = _ := by rw [← he]; ext i; simp

lemma fuses (H : Layout A l B Y) : ∀ i∈Y,seeds S i⊆seeds S A := fun i hi _ hj => H.every.symm ▸ mem_biUnion.mpr ⟨i,hi,hj⟩
lemma home (H : Layout A l B Y) {i : Stores S} (hi : i∈Y) : i.place⊆A.place := by
  rw [← place_reads,← place_reads]; intro j hj; obtain ⟨p,hp,hv⟩ := mem_biUnion.mp hj; exact mem_biUnion.mpr ⟨p,H.fuses _ hi hp,hv⟩
lemma field (H : Layout A l B Y) (d : ℕ) : Y.biUnion (fun i => i.dome d)=A.dome d := by
  ext i; rw [dome,halo_spec, ← place_reads S,H.every,mem_biUnion]; constructor
  · rintro ⟨b,hb,h⟩; obtain ⟨x,hx,h⟩ := halo_spec.mp h
    rw [← place_reads S] at hx; obtain ⟨p,hp,hv⟩ := mem_biUnion.mp hx
    exact ⟨x,mem_biUnion.mpr ⟨p,mem_biUnion.mpr ⟨b,hb,hp⟩,hv⟩,h⟩
  rintro ⟨x,hx,h⟩; obtain ⟨p,hp,hv⟩ := mem_biUnion.mp hx; obtain ⟨b,hb,hp⟩ := mem_biUnion.mp hp
  exact ⟨b,hb,halo_spec.mpr ⟨x, place_reads S b ▸ mem_biUnion.mpr ⟨p,hp,hv⟩, h⟩⟩

lemma points_join (H : Layout A l B Y) {b p} (hb : b∈Y) (hp : p ∈ seeds S A)
    (hx : ¬ Disjoint (b.dome (l*B)) (Packets.points S p)) : p∈seeds S b := by
  rw [H.every] at hp; obtain ⟨x,hx',hp⟩ := mem_biUnion.mp hp
  by_cases h : x=b
  · exact h ▸ hp
  obtain ⟨v,hv,hx⟩ := Finset.not_disjoint_iff.mp hx
  exact False.elim <| Finset.disjoint_left.mp (H.crews hx' hb h) (halo_subset _ x.place
    (place_reads S x ▸ mem_biUnion.mpr ⟨p,hp,hx⟩)) hv

lemma roots_equal (H : Layout A l B Y) : Y=rolls A l B := by
  let s := Y.image (seeds S)
  have hz : s.biUnion id=seeds S A := by rw [H.every,show s=Y.image _ from rfl]; ext; simp
  have hp : Ac.Parts (skin S l B) (seeds S A)=s := by
    rw [← hz]; apply Ac.separates
    · intro i hi; obtain ⟨v,hv,rfl⟩ := mem_image.mp hi; exact H.checkpoints v hv
    intro i hi j hj hk
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hi
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hj
    change Disjoint (support S _ _ _) (support S _ _ _)
    rw [support_reads,support_reads]; exact H.crews hv hw (fun hg => hk (congr_arg _ hg))
  unfold rolls; rw [hp]; unfold s; rw [image_image]; change Y=Y.image (store S ∘ seeds S); rw [show store S ∘ seeds S=id from funext fun i => store_seeds ..,image_id]

open Coat
lemma collects (H : Layout A l B Y) (T : Tube G S) {O : Coat T F} (hf : O.manifest) (he : O.B=B)
    (hO : O.seeds=A) (hl : 500 ≤ l) : ∀ Z∈Y,O.existSeeds Z 300 := by
  intro Z hZ
  have hn : O.B=B := he
  unfold existSeeds; rw [hO,he]; refine ⟨H.home hZ,fun i hi=> ?_⟩
  have hv : RG.flags (temp O.x) O.V=A.flags := hf.symm.trans (hO ▸ rfl)
  rw [hv]
  have hm (Z : Stores S) : Sum.inr (Sum.inr i)∈Packets.seeds S Z ↔ i∈Z.flags := by simp [Packets.seeds]
  constructor
  · intro h; exact (hm A).1 (H.fuses _ hZ ((hm Z).2 h))
  intro h; apply (hm Z).1; apply H.points_join hZ ((hm A).2 h)
  exact Finset.not_disjoint_iff.mpr ⟨i,Lattice.Corona.halo_mono (show 300*B≤l*B from Nat.mul_le_mul_right B (by omega))
    (Finset.Subset.refl _) hi,mem_singleton_self _⟩
end Layout
end YM.ConnectedActivityE6
