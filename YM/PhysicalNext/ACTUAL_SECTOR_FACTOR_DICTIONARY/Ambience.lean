import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Sources

/-!
# The complete raw table read

Stamped even across loose gates; the diagram still gives the literal
coefficients for combinations after clearing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Shipment
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Defenses Voice.Check Parcel SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {ι : Type} [DecidableEq ι] {c f : Side} {S : StepData c f}
variable (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art ι D) (t : ℝ) (h : Lit D) (HZ : Shipment.Valid D ι Z)
local notation "B"=>radiusB D.betaHat
local notation "t₀"=>D.betaHat

variable {F F' : Forest S.ratio} {A A' : Stores S} {b b' : Finset ℕ} {a a' : Finset (Bill S ι)}
    {V V' : Config G c} {k k' : S.Choices} {p p' : Refs G f}
    {X W : Support c} (H : Survey D X W F F' A A' b b' k k' V V' p p')
include H h HZ

private lemma away (i : ℕ) (h0 : halo (700*B) (sourceSites D Z i) ⊆ X) (h1 : floor D (sourceSites D Z i) ⊆ W) :
    surge D Z t i F A b k V p=surge D Z t i F' A' b' k' V' p' := by
  let Y:=sourceSites D Z i
  have ht : ambient D Y ⊆ X := Finset.Subset.trans (Corona.halo_mono (by omega : 40*B≤700*B) (Finset.Subset.refl Y)) h0
  have hm : remote D Y A ↔ remote D Y A' := not_congr (record_at H.fields Y (600*B) le_rfl h.toApp.aperture.scale h0)
  have hx:=(tarp_care D h.toApp Y).outreach ht h1 H
  have hy := (gamma_care h.toApp Y t).outreach ht h1 H
  have hh := (basics D Z h HZ i none).1.outreach ht h1 H
  unfold deck at hh; unfold surge -- not all (cost)
  unfold Y at *; simp only [hm,hx,hy,hh]

omit HZ [DecidableEq ι] in
lemma shiny (i : ListID S) (w : Bool) (h0 : halo (700*B) (Voice.native D i) ⊆ X)
    (h1 : floor D (Voice.native D i) ⊆ W) :
    shine D t i w F A b k V p = shine D t i w F' A' b' k' V' p' := by
  have ht : ambient D (Voice.native D i) ⊆ X := Finset.Subset.trans (Corona.halo_mono (by omega : 40*B≤700*B) (Finset.Subset.refl _)) h0
  have he := (guarded D h.toApp i).outreach ht h1 H
  unfold shine; rw [he]
  cases i with
  | letter i=>
    have hm : remote D (native D (.letter i)) A ↔ remote D (native D (.letter i)) A' := not_congr (record_at H.fields _ (600*B) le_rfl h.aperture.scale h0)
    have hp : Survey D (ambient D (native D (.letter i))) (floor D (native D (.letter i))) F F' A A' b b' k k' V V' p p' :=
      ⟨Geo.Reads.mono H.fields ht,H.input.shrink ht h1,fun i hi=>H.owners i (ht hi)⟩
    dsimp only
    rw [tip_read h.toApp i t hm hp]
  | _=>rfl

lemma option_read (i : Bills S ι) (hn : coat D Z (suggest i) ⊆ X) (hh : wind D Z (suggest i)⊆W) :
    choices D Z t i F A b k V p=choices D Z t i F' A' b' k' V' p' := by
  have h0 := (shelter_option D Z i).trans hn
  let L (Y : Support c) := ambient D Y ⊆ X ∧ floor D Y ⊆W
  have he (Y : Support c) (hi : Y ⊆ sights D Z i) : L Y := ⟨Finset.Subset.trans (Corona.halo_mono (by omega) hi) h0,
    Finset.Subset.trans (Corona.halo_mono le_rfl hi) hh⟩
  rcases i with i|⟨i,u⟩|(i|⟨i,u⟩)|i
  · obtain ⟨hv,hq⟩:=he _ (Finset.Subset.refl (post S i))
    unfold choices; dsimp only; rw [(Check.film D h.toApp i).outreach hv hq H,(tarp_care D h.toApp _).outreach hv hq H]
  · obtain ⟨hv,hq⟩:=he _ (Finset.subset_union_left (s₁:=Voice.native D i))
    exact congr_arg Complex.ofReal (shiny D t h H i u (Finset.Subset.trans (Corona.halo_mono le_rfl Finset.subset_union_left) h0) hq)
  · rfl
  · obtain ⟨hv,hq⟩:=he _ (Finset.subset_union_left (s₁:=sourceSites D Z i))
    unfold choices; dsimp only; rw [(basics D Z h HZ i none).2.2.outreach hv hq H, away D Z t h HZ H _ (Finset.Subset.trans
      (Corona.halo_mono le_rfl Finset.subset_union_left) h0) hq]
  rfl

theorem printed (i : Bill S ι) (hp : coat D Z i⊆ X) (hv : wind D Z i⊆W) (ht : Touch D Z X a a') :
    shutter D Z t i a F A b k V p=shutter D Z t i a' F' A' b' k' V' p' := by
  rcases i with i|i|i
  · exact congr_arg Complex.ofReal (Booklet.comp D Z h.toApp i hp hv H)
  · have hh := (custody_read D Z i).trans hp
    have hl := qualifierAt_eq i (fun j=>ht.scribe i j hh)
    unfold shutter; dsimp only; rw [hl]; apply (basics D Z h HZ i _).2.1.outreach _ hv H
    exact Finset.Subset.trans (Corona.halo_mono (by omega : 40*B ≤ 700*B) (Finset.Subset.refl _)) ((shelter_K D Z i).trans hp)
  exact option_read D Z t h HZ H i hp hv
end YM.PhysicalNext.Dictionary.Shipment
