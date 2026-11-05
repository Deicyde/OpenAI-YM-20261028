import YM.Extra.ITERATION_NO_LOSS.Patterns
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Ambience
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Audition

/-! Assembly diagram pointwise in y on all actual climate slots. Still
before assuming convergence or pricing. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Shipment
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.Sharp
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Defenses Voice.Check Parcel SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {ι : Type} [DecidableEq ι] {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
variable (Z : Art ι D) (t : ℝ) (h : Lit D) (HZ : Shipment.Valid D ι Z)
    (F : Forest S.ratio) (k₀ : S.Choices) (V : Config G c) (A : Stores S) (m : Finset ι)
    (hA : A.flags= RG.flags (temp D.betaHat) V)
local notation "B"=>radiusB D.betaHat
local notation "t₀"=>D.betaHat
local notation "K"=>icons D Z
local notation "H"=>theater D Z h F k₀ V

section area
variable {Q : Finset (Ensign S ι)} (hQ : (icons D Z).Makes A m Q) (k : S.Choices) (y : Room G D.betaHat F A) (i : ↥Q)
include hQ hA HZ
lemma recital (hi : privilege D Z F V i) :
    let r := Ribbon.look ((H).secure A Q m hA hQ i) y
    let u := Print.backdrop t₀ A F y
    let a := Q.biUnion id
    lines D Z t h F k₀ V i k r = ∏ j∈(i.val), shutter D Z t j a F A (Fleet.kSet a) k V u := by
  intro r u a
  unfold lines; rw [if_pos hi]
  let b:=key D Z i.val; let W:=b.near; let X:=(K).X i; let P:=(H).sample i
  have he : Touch D Z X a i := by
    refine ⟨fun j hj=>⟨fun hu=>?_,fun ht=>Finset.mem_biUnion.mpr ⟨i.val,i.property,ht⟩⟩⟩
    obtain ⟨p,hp,hq⟩:=Finset.mem_biUnion.mp hu
    by_cases hr : p=i.val; exact hr ▸ hq
    obtain ⟨w,hw,hl⟩:=Finset.not_disjoint_iff.mp hj
    exact (Finset.disjoint_left.mp (show Disjoint X (wood D Z p) from hQ.1 i.property hp (Ne.symm hr)) hw
      (tent D Z hq hl)).elim
  have ht : Survey D X W F F A P (Fleet.kSet a) (Fleet.kSet i.val) k k V V u (b.embroider r) := by
    refine ⟨Route.Localized.reads hQ _ k i.property hA F, b.identical _ _ ?_,fun _ hv=>he.owner _ hv⟩
    intro e hp
    have hl := Route.Localized.frost (Shipment.nearby D Z) hQ _ i.property hA h.aperture.scale e hp
      (show separation _ _ ≤ _ from (separation_self _).trans_le (Nat.zero_le _))
    exact hl.symm
  exact Finset.prod_congr rfl (fun j hj => (printed D Z t h HZ ht j (tent D Z hj) (needing D Z hj) he).symm)
end area

-- Complex noteField analogue (permission to commute with ∫ separate).
def plume (Q : Finset (Ensign S ι)) (k : S.Choices) (y : Room G t₀ F A) : ℂ :=
    if he : A.flags=RG.flags (temp t₀) V ∧ (K).Makes A m Q then
      ∏ i : Q,lines D Z t h F k₀ V i k (Ribbon.look ((H).secure A Q m he.1 he.2 i) y) else 0

def prints (a : Ensign S ι) : Prop := Shipment.station a=A ∧ signal D Z a=m ∧ permits (requirement D Z F) a

def crude (a : Ensign S ι) (k : S.Choices) (y : Room G t₀ F A) : ℂ :=
  if prints D Z F A m a then ∏ i∈ a,shutter D Z t i a F A (Fleet.kSet a) k V (Print.backdrop t₀ A F y) else 0

lemma scanned (Q : Finset (Ensign S ι)) : (K).ports Q = Shipment.station (Q.biUnion id) := by
  have he : Q.biUnion Fleet.events=Fleet.events (Q.biUnion id) := by ext; simp only [Fleet.events,Finset.mem_biUnion,id_eq]; grind only
  unfold Cards.ports Shipment.station Fleet.scan icons; dsimp only
  rw [← he]; unfold Shipment.station Fleet.scan; congr 1 <;> ext <;> simp

lemma sends (Q : Finset (Ensign S ι)) : Q.biUnion (signal D Z)=signal D Z (Q.biUnion id) := by
  ext; simp only [signal,Finset.mem_biUnion,id_eq]; grind

lemma pad {i : Ensign S ι} (h : Ac.Spark (coat D Z) i) : wood D Z i=region (coat D Z) i := by
  obtain ⟨j,hj⟩:=h.1
  obtain ⟨o,ho⟩:=coat_full D Z j
  exact if_pos ⟨o,Finset.mem_biUnion.mpr ⟨j,hj,ho⟩⟩

lemma separates {Q : Finset (Ensign S ι)} (h : Pieces (coat D Z) Q) :
    (Q:Set (Ensign S ι)).PairwiseDisjoint (K).X := by
  intro i hi j hj ht
  change Disjoint (wood D Z _) (wood D Z _)
  rw [pad D Z (h.2 i hi),pad D Z (h.2 j hj)]; exact h.1 hi hj ht

-- Reconstruct. Negative lookups included in `recital` even when one
-- factor would turn this whole thing off. All marker names jointly routed.
include h HZ hA
theorem prints_iff {a : Ensign S ι} (k : S.Choices) :
    let Q := Ac.Parts (coat D Z) a
    prints D Z F A m a ↔ (K).Makes A m Q ∧ ∀ i∈Q,privilege D Z F V i := by
  intro Q
  have he : Pieces (coat D Z) Q := partition ..
  have hz : Q.biUnion id=a := Ac.reconstruct ..
  have hR := eligible_parts (eligibility D Z k F h.aperture.scale) a
  have hs : (K).ports Q=Shipment.station a := hz ▸ scanned D Z Q
  have hm : Q.biUnion (K).marks=signal D Z a := hz ▸ sends D Z Q
  constructor
  · rintro ⟨h1,h2,h3⟩
    have hx : (K).Makes A m Q := ⟨separates D Z he,hs.trans h1,hm.trans h2⟩
    refine ⟨hx,fun i hi=>⟨he.2 i hi,hR.mp h3 _ hi,?_⟩⟩
    ext x; rw [Finset.mem_inter]
    have ht : A.flags=((K).ports Q).flags := congr_arg Stores.flags hx.2.1.symm
    rw [← hA,ht]
    change x∈wood D Z i ∧ x∈Q.biUnion _ ↔ x∈(Shipment.station i).flags
    rw [Finset.mem_biUnion]
    have h4 (i : Ensign S ι) (hx : x∈(Shipment.station i).flags) : x∈wood D Z i := (K).gate i (Finset.mem_union_right _ hx)
    constructor
    · rintro ⟨hk,j,hj,hz⟩
      by_cases hp : i=j; exact hp.symm ▸ hz
      exact (Finset.disjoint_left.mp (show Disjoint _ _ from hx.1 hi hj hp) hk (h4 j hz)).elim
    exact fun hx=>⟨h4 _ hx,i,hi,hx⟩
  rintro ⟨⟨h₁,h₂,h₃⟩,hp⟩
  exact ⟨hs.symm.trans h₂,hm.symm.trans h₃,hR.mpr (fun i hi=> (hp i hi).2.1)⟩

/-! Termwise square in the spelling diagram; we can now compose with
any raw expansion result in HasSum currency (or reindex by summability
on these *actual* scripts). -/
theorem compose (a : Ensign S ι) (k : S.Choices) (y : Room G t₀ F A) :
    plume D Z t h F k₀ V A m (Ac.Parts (coat D Z) a) k y = crude D Z t F V A m a k y := by
  unfold plume crude; let p:= Print.backdrop t₀ A F y; let P':=Ac.Parts (coat D Z) a
  let f i := shutter D Z t i a F A (Fleet.kSet a) k V p
  have he := prints_iff D Z h HZ F V A m hA (a:=a) k
  have hs: P'.biUnion id=a := Ac.reconstruct ..
  have ht : Pieces (coat D Z) P' := partition ..
  split_ifs with hX hY hY
  · let read (i : ↥P') := Ribbon.look ((H).secure A P' m hX.1 hX.2 i) y
    have hy (i : ↥P') : lines D Z t h F k₀ V i k (read i) = ∏ j∈i.val,f j := by
      have hl := recital D Z t h HZ F k₀ V A m hA hX.2 k y i ((he.mp hY).2 i.val i.property)
      unfold P' at hs; simpa only [hs] using! hl
    change ∏ i : P',lines D Z t h F k₀ V i k (read i) = _
    simp_rw [hy]
    change (∏ i : P',∏ j ∈ i.val, _)= ∏ j ∈ a,f j
    calc
      _ = ∏ i∈P',∏ j∈i, f j := Finset.prod_coe_sort P' (fun i=> ∏ j∈i,f j)
      _ = ∏ j∈P'.biUnion id,f j:= (Finset.prod_biUnion (no_duplicate _ (coat_full D Z) ht.1)).symm
      _ = _:=congr_arg (fun i=> ∏ j∈i, f j) hs
  · have hv : ¬∀ i∈P',privilege D Z F V i := fun h'=>hY (he.mpr ⟨hX.2,h'⟩)
    push Not at hv
    obtain ⟨i,hi,hh⟩ := hv
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hi⟩:P'))
    exact if_neg hh
  · exact (hX ⟨hA,(he.mp hY).1⟩).elim
  · rfl

omit hA HZ in
lemma miss {Q : Finset (Ensign S ι)} (hi : ¬Pieces (coat D Z) Q) (k : S.Choices) (y : Room G t₀ F A) :
    plume D Z t h F k₀ V A m Q k y=0 := by
  unfold plume; split
  next hv =>
    suffices h : ∃ i∈Q,¬Ac.Spark (coat D Z) i by
      obtain ⟨i,hp,hs⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hp⟩ : Q))
      exact if_neg (fun hx=>hs (show Ac.Spark (coat D Z) i from (show privilege D Z F V i from hx).1))
    by_contra! hh
    refine hi ⟨?_,hh⟩
    intro i hx j hy ht
    change Disjoint (region _ i) (region _ j)
    rw [← pad D Z (hh i hx),← pad D Z (hh j hy)]; exact hv.2.1 hx hy ht
  rfl

/-- Verified `Words.reindex` on this currency. No generic Gaussian
factorization waiting between the equality cost and the actual climate.
-/
theorem diagram (k : S.Choices) (y : Room G t₀ F A) (z : ℂ) :
    HasSum (fun a=>crude D Z t F V A m a k y) z ↔ HasSum (fun Q=>plume D Z t h F k₀ V A m Q k y) z :=
  reindex (fun i hi=>miss D Z t h F k₀ V A m hi k y) (fun i=>compose D Z t h HZ F k₀ V A m hA i k y)
end YM.PhysicalNext.Dictionary.Shipment
