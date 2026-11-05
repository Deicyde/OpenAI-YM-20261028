import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Memo

/-! Complete physical eligibility. Includes exclusion relations even
on zero extensions. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
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
    (Z : Art ι D)
local notation "B"=>radiusB D.betaHat
local notation "t₀"=>D.betaHat

def hasVersions : ListID S → Bool
  | .letter _=> true
  | _ => false

/- permitted here on actual Store and b. `remote` only affects value, so
retain both marks even if the dictionary's primary=zero on this Store. -/
def election (F : Forest S.ratio) (A : Stores S) (b : Finset ℕ) : Bills S ι → Prop
  | .inl i => live t₀ F A b (.inl i) ∧ ¬ wanted S t₀ A i
  | .inr (.inl (i,l)) => present t₀ A F i ∧ ¬wants D A i ∧ (l=false ∨ hasVersions i=true)
  | .inr (.inr (.inl (.inl _))) => True
  | .inr (.inr (.inl (.inr (i,l)))) => (Z.names i).Nonempty
  | .inr (.inr (.inr i)) => i.1∈b ∧ (Z.sig i.1 i.2).Nonempty

def requirement (F : Forest S.ratio) (i : Bill S ι) (s : Finset (Bill S ι)) :=
    Fleet.required S D.labels (hump B) question i s ∧
      (match i with
       | .inr (.inr j) => election D Z F (station s) (Fleet.kSet s) j
       | _=>True) ∧ ∀ j∈s, j≠i → Disjoint (burst D Z i) (burst D Z j)

variable {F F' : Forest S.ratio} {A A' : Stores S} {V V' : Config G c} {k k' : S.Choices}
    {X : Support c} (h : Physical.Reads X A A' F F' V V' k k')
include h
lemma screen_at (i : Voice.Check.Test c f) (b b' : Finset ℕ) (ht : ambient D (post S i) ⊆ X) (he : 120≤B) :
    live t₀ F A b (.inl i) ↔ live t₀ F' A' b' (.inl i) := by
  cases i with
  | screen i=>
    exact h.frozen_bits he _ (widen' ((covers_shield (40*B) (at_post (S:=S) (Test.screen i))).shrink (by omega)) ht)
  | _=>exact Iff.rfl

lemma present_at (i : ListID S) (ht : ambient D (Voice.native D i)⊆X) (he : 120≤B) :
    present t₀ A F i ↔ present t₀ A' F' i := by
  have hh (j : Bond f) (hi : portOf S j∈ Voice.native D i) := Geo.widen' ((covers_shield (40*B) hi).shrink (by omega : 12*B≤40*B)) ht
  cases i with
  | glaze i=> exact h.frozen_bits he i (hh i (Finset.mem_singleton_self _))
  | deficit i=> exact Print.winter_read t₀ h i he (hh i (Finset.mem_singleton_self _))
  | spark i j n=>
    have hv := hh i (Finset.mem_insert_self ..)
    have hx := hh j (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    exact and_congr (h.frozen_bits he i hv) (h.frozen_bits he j hx)
  | surge i=>exact h.frozen_bits he i (hh i (Finset.mem_singleton_self _))
  | _=> exact Iff.rfl

lemma elected (i : Bills S ι) {s t : Finset ℕ}
    (hn : ∀ i,custody D i⊆ X → (i∈s↔i∈t)) (hp : coat D Z (suggest i) ⊆ X) (ht : 120≤B) :
    election D Z F A s i ↔ election D Z F' A' t i := by
  have hh := (shelter_option D Z i).trans hp
  have hf (P : Support c) (he : P⊆sights D Z i) (k : ℕ) (hk : k≤700*B) : halo k P ⊆ X :=
    fun z hz => hh (Corona.halo_mono hk he hz)
  rcases i with i|⟨i,l⟩|(i|i)|⟨i,j⟩
  · refine and_congr (screen_at D h i s t (hf _ (Finset.Subset.refl _) _ (by omega)) ht)
      (not_congr (record_at h _ _ (z:=B) (by gcongr; exact (fare i).trans (by omega)) ht (hf _ (address_le i) _ le_rfl)))
  · exact and_congr (present_at D h i (hf _ Finset.subset_union_left _ (by omega)) ht)
      (and_congr_left (fun _=> not_congr (record_at h _ _ (z:=B) (by gcongr; exact (answer i).trans (by omega)) ht (hf _ Finset.subset_union_right _ le_rfl))))
  · rfl
  · rfl
  exact and_congr_left (fun _=> hn i (fun x hi=>hp (option_sights D Z (qualify i j) (Finset.mem_union_left _ hi))))

omit h in
lemma eligibility (k : S.Choices) (F : Forest S.ratio) (hp : 120≤B) : Retained (coat D Z) (requirement D Z F) := by
  intro i a b H
  unfold requirement
  have hz := Fleet.stationed D.labels (hump B) (question (S:=S) (ι:=ι)) (coat D Z) (shelter_packet D Z)
    (fun i=>Finset.Subset.trans (custody_post D i) (custody_read D Z i)) (inspected_names D Z) i a b H -- fix
  rw [hz]
  apply propext; refine and_congr_right (fun _=>and_congr ?_ ?_)
  · rcases i with i|i|i
    · rfl
    · rfl
    have ht : Touch D Z (coat D Z (suggest i)) a b:=⟨H⟩
    exact elected D Z (ht.reads F (1:Config G c) k) i ht.know (Finset.Subset.refl _) hp
  refine forall_congr' (fun j=>?_); by_cases he : j=i
  · simp [he]
  simp only [he, ne_eq, not_false_eq_true, true_implies]
  by_cases hh : Disjoint (burst D Z i) (burst D Z j)
  · simp [hh]
  obtain ⟨l,hl,ht⟩:= Finset.not_disjoint_iff.mp hh
  rw [H _ (Finset.not_disjoint_iff.mpr ⟨_,owner_reserve D Z i l hl,owner_reserve D Z j l ht⟩)]
end YM.PhysicalNext.Dictionary.Shipment
