import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Shipments

/-! Table lookups. If a seed/flag/qualifier answer differs from
off-world, the witness packet/slot intersects this footprint.
Don't use that test as if it were a test that the underlying gates
hold. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Shipment
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Check Parcel SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {ι : Type} [DecidableEq ι] {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
variable (Z : Art ι D)
local notation "B"=>radiusB D.betaHat

lemma shelter_packet (u : Fleet.Packet c f) :
    region (Fleet.spans S (hump B)) u ⊆ coat D Z (pack u) := certain _
lemma shelter_K (i : ℕ) : halo (700*B) (custody D i) ⊆ coat D Z (known i) := certain _
lemma shelter_option (i : Bills S ι) : halo (700*B) (sights D Z i) ⊆ coat D Z (suggest i) := certain _
lemma option_sights (i : Bills S ι) : sights D Z i ⊆ coat D Z (suggest i) := Finset.Subset.trans (halo_subset ..) (shelter_option D Z i)
lemma custody_post (i : ℕ) : (D.labels.forced i).support.image S.ratio.parent ⊆ custody D i := by
  intro x hx; obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
  exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ hy)
lemma custody_read (i : ℕ) : custody D i ⊆ coat D Z (known i) := Finset.Subset.trans (halo_subset ..) (shelter_K D Z i)

-- Key pair will meet once even if physical anchor queries all absent.
-- Every K tests authorization bits at every changing mark address,
-- inclusive of origins even at dormant, no converses assumed there.
lemma holdings (i : ℕ) : (custody D i).Nonempty := by
  obtain ⟨j,hj⟩:=(D.labels.forced i).inventory_ne
  exact ⟨_,custody_post D i (Finset.mem_image_of_mem S.ratio.parent ((D.labels.forced i).inventory_sup hj))⟩


variable {a b : Finset (Bill S ι)} {X : Support c}

def station (v : Finset (Bill S ι)) : Stores S := Fleet.scan (Fleet.events v)

structure Touch (X : Support c) (a b : Finset (Bill S ι)) : Prop where
  mentions i : ¬Disjoint X (coat D Z i) → (i∈a ↔ i∈b)

namespace Touch
variable {D Z} (t : Touch D Z X a b)
include t
lemma small {Y : Support c} (h : Y⊆X) : Touch D Z Y a b where
  mentions i ht:= t.mentions i (fun hb=>ht (Finset.disjoint_of_subset_left h hb))

lemma scribe (i j : ℕ) (h : custody D i ⊆ X) : suggest (qualify i j) ∈ a ↔ suggest (qualify i j) ∈ b := by
  obtain ⟨o,hx⟩:= holdings D i
  exact t.mentions _ (Finset.not_disjoint_iff.mpr ⟨o,h hx,option_sights D Z _ (Finset.mem_union_left _ hx)⟩)
lemma know (v : ℕ) (h : custody D v ⊆ X) : v∈Fleet.kSet a ↔ v∈Fleet.kSet b := by
  obtain ⟨o,hv⟩:= holdings D v
  simp only [Fleet.kSet,Finset.mem_toLeft,Finset.mem_toRight]
  exact t.mentions (known v) (Finset.not_disjoint_iff.mpr ⟨o,h hv,custody_read D Z v hv⟩)
lemma owner (i : Site f) (hi : S.ratio.parent i∈X) : i∈D.Owners (Fleet.kSet a) ↔ i∈ D.Owners (Fleet.kSet b) := by
  unfold Desk.Owners
  simp only [Finset.mem_biUnion]
  refine exists_congr fun j=> and_congr_left (fun hj => ?_)
  simp only [Fleet.kSet,Finset.mem_toLeft,Finset.mem_toRight]
  exact t.mentions (known j) (Finset.not_disjoint_iff.mpr ⟨_,hi,custody_read _ _ _ (custody_post D j (Finset.mem_image_of_mem _ hj))⟩)

lemma seed (v : Fleet.Seed c f) (i : Site c) (hx : i∈X) (he : i∈ Fleet.whereAt S v) : v∈Fleet.events a ↔ v∈Fleet.events b := by
  simp only [Fleet.list_events,Finset.mem_biUnion,Finset.mem_toLeft,id_eq]
  refine exists_congr fun P=> and_congr_left (fun h => ?_)
  have hh : i ∈ coat D Z (pack P) := shelter_packet D Z P (Finset.mem_biUnion.mpr ⟨v,h,halo_subset _ _ he⟩)
  exact t.mentions (pack P) (Finset.not_disjoint_iff.mpr ⟨i,hx,hh⟩)

lemma reads (F : Forest S.ratio) (V : Config G c) (k : S.Choices) :
    Physical.Reads X (station a) (station b) F F V V k k := by
  refine ⟨fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>Iff.rfl,fun i hi=>?_,fun i hi=>?_,fun i hi=>?_⟩
  · simp only [station,Fleet.scan,Finset.mem_toRight]
    exact t.seed _ i (hi (Finset.mem_union_left _ (Finset.mem_singleton_self i))) (Finset.mem_singleton_self _)
  · simp only [station,Fleet.scan,Finset.mem_toLeft]
    have hx:= at_post (S:=S) (Test.fine i)
    exact t.seed _ _ (hi hx) hx
  simp only [station,Fleet.scan,Finset.mem_toLeft,Finset.mem_toRight]
  exact t.seed _ _ (hi (Finset.mem_insert_self ..)) (Finset.mem_insert_self ..)
end Touch

section sector
variable {F F' : Forest S.ratio} {A A' : Stores S} {V V' : Config G c} {k k' : S.Choices} (h : Physical.Reads X A A' F F' V V' k k')
include h
lemma record_at (P : Support c) (r : ℕ) {z : ℕ} (hp : r≤600*z) (hz : 120 ≤ z)
    (hh : halo (700*z) P ⊆ X) : recorded S P r A ↔ recorded S P r A' := by
  unfold Parcel.recorded; simp only [Finset.not_disjoint_iff]
  refine exists_congr fun i=> and_congr_right fun ht=> h.dome_agrees _ _ ?_
  exact fun j hj => hh (halo_spec.mpr ⟨i,ht,hj.trans (by omega)⟩)
end sector

lemma inspected_names (i j : Bills S ι) (he : question j=question i) : ¬Disjoint (coat D Z (suggest i)) (coat D Z (suggest j)) := by
  rcases i with i|⟨i,t⟩|(i|⟨i,t⟩)|⟨i,l⟩ <;> rcases j with j|⟨j,s⟩|(j|⟨j,s⟩)|⟨j,m⟩ <;>
    simp only [question,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at he
  all_goals subst j
  · obtain ⟨w,hw⟩:=coat_full D Z (suggest (supplement i)); exact Finset.not_disjoint_iff.mpr ⟨w,hw,hw⟩
  · have hh : coat D Z (suggest (accent i s))=coat D Z (suggest (accent i t)) := rfl
    change ¬Disjoint _ (coat D Z (suggest (accent i s))); rw [hh]
    obtain ⟨w,hw⟩:=coat_full D Z (suggest (accent i t)); exact Finset.not_disjoint_iff.mpr ⟨w,hw,hw⟩
  · obtain ⟨w,hw⟩:=coat_full D Z (suggest (Shipment.singleton i)); exact Finset.not_disjoint_iff.mpr ⟨w,hw,hw⟩
  · have hh : coat D Z (suggest (bead i s))=coat D Z (suggest (bead i t)) := rfl
    change ¬Disjoint _ (coat D Z (suggest (bead i s))); rw [hh]
    obtain ⟨w,hw⟩:=coat_full D Z (suggest (bead i t)); exact Finset.not_disjoint_iff.mpr ⟨w,hw,hw⟩
  obtain ⟨o,ho⟩:=holdings D i
  exact Finset.not_disjoint_iff.mpr ⟨o,option_sights D Z (qualify i l) (Finset.mem_union_left _ ho),
    option_sights D Z (qualify i m) (Finset.mem_union_left _ ho)⟩
end YM.PhysicalNext.Dictionary.Shipment
