import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Audition

/-! Ways a reading occurs; keep the portal in billing correspondence.
Works also in the presence of marked options, retaining the unmarked
read products and carrying the extra in the same Display.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Lobbies
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.Sharp
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Defenses Voice.Check Parcel Shipment SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {ι : Type} [DecidableEq ι] {c f : Side} {S : StepData c f}
variable (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art ι D) (t : ℝ) (h : Lit D)
    {F : Forest S.ratio} {A : Stores S} (a : Ensign S ι)
local notation "B"=>radiusB D.betaHat
local notation "t₀"=>D.betaHat

/-- Common sector validity for everything in a or a component-dug
portion. Allows the *sample* flags. -/
structure Casting (F : Forest S.ratio) (A : Stores S) : Prop where
  legal : permits (requirement D Z F) a
  seed : ∀ i∈Fleet.events a,i ∈ Fleet.manifest A
  chooses i : suggest i ∈ a → election D Z F A (Fleet.kSet a) i

namespace Casting
variable {D Z a} (C : Casting D Z a F A)
include C
-- Trajectory inputs determined once.
lemma coarse : permits (Fleet.required S D.labels (hump B) question) a := fun i hi=> (C.legal i hi).1
lemma connected : Pieces (Fleet.spans S (hump B)) a.toLeft := ((Fleet.classified ..).mp C.coarse).1
lemma origins : Fleet.origins D.labels (Shipment.station a) (Fleet.kSet a) := ((Fleet.classified ..).mp C.coarse).2.1
lemma tickets {i j : Bills S ι} (hi : suggest i∈a) (hj : suggest j∈a) (hr : question i=question j) : i=j :=
  ((Fleet.classified ..).mp C.coarse).2.2 _ (Finset.mem_toRight.mpr (Finset.mem_toRight.mpr hj)) _
    (Finset.mem_toRight.mpr (Finset.mem_toRight.mpr hi)) hr
lemma publishes {p} (hp : pack p∈a) {q : Support c} {r} (h : levied S q r p) : recorded S q r A := by
  obtain ⟨x,hx,hl⟩:= Finset.not_disjoint_iff.mp h
  obtain ⟨i,hi,hx'⟩:=Finset.mem_biUnion.mp hl
  obtain ⟨w,hw,hz⟩:=halo_spec.mp hx'
  refine (records ..).mpr ⟨x,hx,w,(manifest_spot w A).mpr ⟨i,C.seed _ (Finset.mem_biUnion.mpr ⟨pack p,hp,hi⟩),hw⟩,hz⟩


omit C in
def unmarked (F : Forest S.ratio) (a : Ensign S ι) (h : permits (requirement D Z F) a) : Casting D Z a F (Shipment.station a) where
  legal := h
  seed i hi := by rw [Shipment.station,Fleet.record]; exact hi
  chooses i hi := (h _ hi).2.1

-- Any allowed component with V set correctly profits at its *fixed*
-- roster sample, even though flags are part of the wider Store.
omit C in
def crew (h : Lit D) (F : Forest S.ratio) (V : Config G c) (a : Ensign S ι) (k : S.Choices) (hi : privilege D Z F V a) :
    Casting D Z a F (Route.patch t₀ V (Shipment.station a)) where
  legal := hi.2.1
  seed i hi' := by
    have ht : i∈Fleet.manifest (Shipment.station a) := by rw [Shipment.station,Fleet.record]; exact hi'
    let A:=Shipment.station a
    suffices Fleet.manifest A⊆Fleet.manifest (Route.patch t₀ V A) from this ht
    unfold Fleet.manifest Route.patch; simp only
    intro i; rcases i with i|i|i <;> simp only [Finset.inl_mem_disjSum,Finset.inr_mem_disjSum] <;> intro hx <;> try exact hx
    exact (Finset.mem_inter.mp (hi.2.2.symm ▸ (show i∈ (Shipment.station a).flags from hx))).2
  chooses i hK := by
    let Q:=Shipment.station a
    have hx : Physical.Reads (wood D Z a) Q (Route.patch t₀ V Q) F F V V k k := by
      refine ⟨fun _ _ _=>rfl,fun _ _=>rfl,fun _ _ => rfl, fun _ _ _=>Iff.rfl,fun i ht=>?_,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩ -- .bond two args
      have hn:=ht (show i∈inspected ({i}:Support c) from Finset.mem_union_left _ (Finset.mem_singleton_self _))
      change i∈(Shipment.station a).flags ↔ i∈RG.flags (temp t₀) V
      rw [← hi.2.2]; simp only [Finset.mem_inter,hn,true_and]
    exact (elected D Z hx i (fun _ _=>Iff.rfl) (tent D Z hK) h.aperture.scale).mp ((hi.2.1 _ hK).2.1)
end Casting

section steps

abbrev optionalTests := (Fleet.addSet a).toLeft
abbrev alternates := (Fleet.addSet a).toRight.toLeft
abbrev plumage (A : Stores S) (F : Forest S.ratio) := a.toLeft.biUnion (fun p=>Booklet.checks D p F A)
abbrev paper (A : Stores S) (F : Forest S.ratio) := a.toLeft.biUnion (fun p=>Booklet.history D p F A)
abbrev vacuum := (Fleet.kSet a).filter (fun i=> Shipment.qualifierAt a i=none)
abbrev major (A : Stores S) (F : Forest S.ratio) := (plumage D a A F ∪ optionalTests a).disjSum (vacuum a)
abbrev specials := (alternates a).filter (fun i=>hasVersions i.1=true)
abbrev everyday := (alternates a).filter (fun i=>hasVersions i.1=false)

variable {D Z a} (C : Casting D Z a F A)

lemma test_present {i : Voice.Check.Test c f} (hi : i∈optionalTests a) : suggest (supplement i)∈a := by
  simpa only [optionalTests,Fleet.addSet,Finset.mem_toLeft,Finset.mem_toRight] using hi
lemma panel_present {i : ListID S} {b : Bool} (hi : (i,b)∈alternates a) : suggest (accent i b)∈a := by
  simpa only [alternates,Fleet.addSet, Finset.mem_toRight,Finset.mem_toLeft] using hi
include C
lemma free {i : Voice.Check.Test c f} (hi : i∈optionalTests a) : live t₀ F A (Fleet.kSet a) (.inl i) ∧ ¬wanted S t₀ A i :=
  C.chooses _ (test_present hi)
lemma reserved {i : Voice.Check.Test c f} (he : i∈plumage D a A F) : live t₀ F A (Fleet.kSet a) (.inl i) ∧ wanted S t₀ A i := by
  obtain ⟨j,hj,hp⟩:=Finset.mem_biUnion.mp he
  obtain ⟨ht,hh⟩ := (show _ ∧ levied S (address S i) _ j from (Finset.mem_filter.mp hp).2)
  exact ⟨by cases i <;> exact ht,C.publishes (Finset.mem_toLeft.mp hj) hh⟩
lemma registered {i : Voice.Check.Test c f ⊕ ℕ} (hi : i∈major D a A F) : live t₀ F A (Fleet.kSet a) i := by
  rcases i with i|i
  · rcases Finset.mem_union.mp (Finset.inl_mem_disjSum.mp hi) with he|he
    · exact (Lobbies.reserved C he).1
    exact (Lobbies.free C he).1
  exact (Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hi)).1
lemma worlds {i} {b} (hi : (i,b)∈alternates a) : present t₀ A F i ∧ ¬wants D A i ∧ (b=false ∨ hasVersions i=true) :=
  C.chooses _ (panel_present hi)
lemma press {i} (hi : i∈paper D a A F) : present t₀ A F i ∧ wants D A i := by
  obtain ⟨j,hj,ht⟩:= Finset.mem_biUnion.mp hi
  obtain ⟨hX,hY⟩ := (show _ ∧ levied S _ _ _ from (Finset.mem_filter.mp ht).2)
  exact ⟨hX,C.publishes (Finset.mem_toLeft.mp hj) hY⟩
lemma variant {i} {b b'} (hi : (i,b)∈alternates a) (hj : (i,b')∈alternates a) : b=b' := by
  have he := C.tickets (panel_present hi) (panel_present hj) (show question (S:=S) (ι:=ι) (accent i b)=question (accent i b') from rfl)
  simpa [accent] using he
end steps
end YM.PhysicalNext.Dictionary.Lobbies
