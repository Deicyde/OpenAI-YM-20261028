import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Ambience
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Cue

/-! All standard Reading location tests at the unchanged badge. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Lobbies
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.Sharp
open AnalyticBridge.LocalGaussian Spot Spot.Programme
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Defenses Voice.Check Parcel Shipment SectorNext.Reconnect SectorNext.Reconnect.Words Casting
variable {G : Gauge} {ι : Type} [DecidableEq ι] {c f : Side} {S : StepData c f}
variable (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art ι D) (t : ℝ) (h : Lit D)
    {F : Forest S.ratio} {A : Stores S} {a : Ensign S ι} (C : Casting D Z a F A) (k₀ k : S.Choices)

local notation "B"=>radiusB D.betaHat
local notation "u₀"=>chosen D F k₀ A k
local notation "X"=>wood D Z a
local notation "w₀"=>Shipment.key D Z a
local notation "porthole" => Route.Badge.lens D F (Native.kinetic D.tube F k₀ D.betaHat) A k (Shipment.key D Z a)
local notation "j₀" => Route.Badge.offer D F (Native.kinetic D.tube F k₀ D.betaHat) A k (Shipment.key D Z a) (Lit.toApp h)

/- Each of these gems in a relevant formula respects **every** read
constraint. Keep the frame regardless of the turnout at this V. -/
def Visit {R : Type*} [MeasurableSpace R] (f : Formula G S R) (a : Ensign S ι) (F : Forest S.ratio) (A : Stores S) : Prop :=
    Measurable (uncurry (f F A (Fleet.kSet a) k)) ∧ ∀ (U V : Config G c), Agrees (wood D Z a) U V →
      ∀ p p' : Geo.Refs G _, Geo.Same S (wood D Z a) (region (wind D Z) a) p p' →
        f F A (Fleet.kSet a) k U p=f F A (Fleet.kSet a) k V p'

lemma Visit.fromCare {R : Type*} [MeasurableSpace R] (f : Formula G S R) {Y} (hp : Care D Y f)
    (hf : ambient D Y⊆X) (hz : Voice.floor D Y⊆region (wind D Z) a) : Visit D Z k f a F A :=
    ⟨hp.noted ..,fun _ _ hv _ _ ht=>hp.outreach hf hz ⟨⟨hv,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>Iff.rfl,fun _ _=>Iff.rfl,
       fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩,ht,fun _ _=>Iff.rfl⟩⟩

include h C

private lemma visits_gate (i : major D a A F) :
    Visit D Z k (latch D i.val) a F A := by
  obtain ⟨i,hi⟩:=i
  rcases i with i|i
  · rcases (show i∈plumage D a A F ∪ optionalTests a from Finset.inl_mem_disjSum.mp hi) |> Finset.mem_union.mp with h0|h0
    · have hr := (Lobbies.reserved C h0).2
      obtain ⟨v,hv,hq⟩:= Finset.mem_biUnion.mp h0
      obtain ⟨ht,h₁⟩ := Shipment.packet_test D Z h.aperture.scale (p:=v) (i:=i) ((Finset.mem_filter.mp hq).2.2)
      have he : pack v ∈ a:= Finset.mem_toLeft.mp hv
      unfold Visit latch; dsimp only; simp only [hr,↓reduceIte]
      exact Visit.fromCare D Z k _ (Check.film D h.toApp i) (ht.trans (Shipment.tent D Z he))
        (h₁.trans (Shipment.needing D Z he)) -- `..` usage
    have hr := (Lobbies.free C h0).2
    have ht : suggest (supplement i) ∈ a := test_present h0
    have hx : ambient D (post S i)⊆wood D Z a := Finset.Subset.trans (Corona.halo_mono (by omega) (Finset.Subset.refl _))
      ((Shipment.shelter_option D Z (supplement i)).trans (Shipment.tent D Z ht))
    have hv : Voice.floor D (post S i)⊆region (wind D Z) a:= Shipment.needing D Z ht
    unfold Visit latch; dsimp only; simp only [hr,↓reduceIte]
    apply Visit.fromCare D Z k _ _ hx hv
    apply Care.together (Care.follows (Check.film D h.toApp i) (fun r:ℝ=>r-1) (by fun_prop))
      (v:=fun F A b k V p => if Parcel.bare i then tarp D (post S i) F A b k V p else 1) -- defeq ite binder differs
    split
    · exact tarp_care D h.toApp _
    exact Care.constant 1
  have ht : i∈Fleet.kSet a := (Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hi)).1
  have he : known i∈a := by simpa only [known,Fleet.kSet, Finset.mem_toLeft,Finset.mem_toRight] using ht
  exact Visit.fromCare D Z k _ (Care.together (packed D h.toApp i) (tarp_care D h.toApp _))
    (Finset.Subset.trans (Corona.halo_mono (by omega) (Finset.Subset.refl _)) ((shelter_K D Z i).trans (Shipment.tent D Z he)))
    (Shipment.needing D Z he)

private lemma cadence {i : ListID S} {r : Bool} (hi : (i,r)∈alternates a) :
    halo (700*B) (Voice.native D i) ⊆ X ∧ Voice.floor D (Voice.native D i) ⊆region (wind D Z) a :=
  let l := panel_present hi
  ⟨Finset.Subset.trans (Corona.halo_mono le_rfl Finset.subset_union_left)
    ((Shipment.shelter_option D Z (accent i r)).trans (Shipment.tent D Z l)),
    Finset.Subset.trans (Corona.halo_mono le_rfl Finset.subset_union_left) (Shipment.needing D Z l)⟩

private lemma visits_lobby (i : Alien (D:=D) (F:=F) (A:=A) (a:=a)) : Visit D Z k (lounge t i) a F A := by
  rcases i with i|i
  · exact visits_gate D Z h C k i
  have he:= (lead i).property
  obtain ⟨h1,h2⟩:=cadence D Z h C he
  constructor
  · -- shine uncast
    have hm := ((((guarded D h.toApp (.letter (title i))).noted F A (Fleet.kSet a) k).exp.sub (measurable_const (a:=(1:ℝ))))) -- needs i.val.1
    change Measurable (uncurry (shine D t i.val.1 i.val.2 F A (Fleet.kSet a) k))
    rw [Casting.title_way i]
    unfold uncurry shine; dsimp only; split
    next hr => exact hm.sub (tip_meas h.toApp _ t ..)
    exact tip_meas h.toApp _ t F A _ k
  intro U V hv p p' hp
  exact shiny D t h ⟨⟨hv,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>Iff.rfl, fun _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩,
    hp,fun _ _=>Iff.rfl⟩ i.val.1 i.val.2 h1 h2

private lemma visits_podium (i : paper D a A F) : Visit D Z k (sew D i.val) a F A := by
  obtain ⟨j,hj,hm⟩:=Finset.mem_biUnion.mp i.property
  obtain ⟨ht,he⟩:= Shipment.packet_log D Z h.aperture.scale (p:=j) (i:=i.val) ((Finset.mem_filter.mp hm).2.2)
  exact Visit.fromCare D Z k (F:=F) _ (local_series D h.toApp i.val) (ht.trans (Shipment.tent D Z (Finset.mem_toLeft.mp hj)))
    (he.trans (Shipment.needing D Z (Finset.mem_toLeft.mp hj)))

private lemma visits_dialogue (i : everyday a) : Visit D Z k (introduce D i.val.1) a F A := by
  obtain ⟨ht,he⟩:=cadence D Z h C (dial i).property
  exact Visit.fromCare D Z k _ (guarded D h.toApp _) (Finset.Subset.trans (Corona.halo_mono (by omega) (Finset.Subset.refl _)) ht) he

omit C h in
private lemma clarifies {R : Type} [MeasurableSpace R] {f : Formula G S R}
    (hr : Visit D Z k f a F A) :
    let g (V : Config G c) (p : (w₀).Person D F A) := f F A (Fleet.kSet a) k V ((w₀).embed D F A p)
    Measurable (uncurry g) ∧ LocalOn (wood D Z a) g ∧
      ∀ V p,g V ((porthole).info p)= f F A (Fleet.kSet a) k V (Print.backdrop D.betaHat A F p) := by
  intro g
  refine ⟨hr.1.comp (f:=fun p : Config G c × Route.Badge.Person D F A (Shipment.key D Z a) =>
    (p.1,(w₀).embed D F A p.2)) (measurable_fst.prodMk (((w₀).embed_meas D F A).comp measurable_snd)),
    fun U V hp=>funext fun p=>hr.2 U V hp _ _ ⟨fun _ _ _=>rfl,fun _ _ _=>rfl⟩,fun V p=>?_⟩
  exact (hr.2 V V (fun _ _ _=>rfl) _ _ ((w₀).snap D F _ A k p)).symm

-- One Reading for the skeleton. At all flags & configurations as
-- required by the two interfaces; no shrinking V to a chart.
def showtime : Reading (j₀) (port C k₀ k h t) where
  ret i V p:= lounge t i F A (Fleet.kSet a) k V ((w₀).embed D F A p)
  logs i V p:= sew D i.val F A (Fleet.kSet a) k V ((w₀).embed D F A p)
  delta i V p:= introduce D i.val.1 F A (Fleet.kSet a) k V ((w₀).embed D F A p)
  retMeas i:= (clarifies D Z k₀ k (visits_lobby D Z t h C k i)).1
  logsMeas i:= (clarifies D Z k₀ k (visits_podium D Z h C k i)).1
  deltaMeas i:= (clarifies D Z k₀ k (visits_dialogue D Z h C k i)).1
  retSees i:= (clarifies D Z k₀ k (visits_lobby D Z t h C k i)).2.1
  logsSee i:= (clarifies D Z k₀ k (visits_podium D Z h C k i)).2.1
  deltaSees i:= (clarifies D Z k₀ k (visits_dialogue D Z h C k i)).2.1
  retReached i V p hV:= ((clarifies D Z k₀ k (visits_lobby D Z t h C k i)).2.2 V p).trans (Casting.stays t h C k₀ k V i)
  logsReached i V p hV:= ((clarifies D Z k₀ k (visits_podium D Z h C k i)).2.2 V p).trans (Casting.podium t h C k₀ k V i)
  deltaReached i V p hV:= ((clarifies D Z k₀ k (visits_dialogue D Z h C k i)).2.2 V p).trans (Casting.speaks t h C k₀ k V i)

end YM.PhysicalNext.Dictionary.Lobbies
