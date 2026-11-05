import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Marginals
import YM.SectorNext.RECONNECTED_LOCALITY.Lodge

/-! Read currency for one ordered occurrence of the multiplier. `heart` is
the pre-gather location of that occurrence; use `ambient` also for every
potential Y,k,etc. answer and `floor` for all Z requests, optionally
patching every regular argument within `floor`, never *all those in a
much larger component* as an individual accounting shortcut.

Here, for instance, every actual hard U & Z argument in the
physical numerical equality must be tested, not only those on the
support of the realized complement. Still to retain also eligibility
and forced catalogue checks, e.g. compulsory radius 300B & complete
K incidences, use larger support in collection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Voice
open Wires Geo 
variable {G : Gauge} {c f : Side} {S : StepData c f} {d : AnalyticBridge.LocalGaussian.Desk G S}

abbrev Formula (G : Gauge) (S : StepData c f) (R : Type*) := Forest S.ratio → Stores S → Finset ℕ →
    S.Choices → Config G c → Refs G f → R

def floor (d : AnalyticBridge.LocalGaussian.Desk G S) (l : Support c) := halo (15*radiusB d.betaHat) l

def ambient (d : AnalyticBridge.LocalGaussian.Desk G S) (l : Support c) := halo (40*radiusB d.betaHat) l

structure Survey (d : AnalyticBridge.LocalGaussian.Desk G S) (X W : Support c)
    (F F' : Forest S.ratio) (A A' : Stores S) (b b' : Finset ℕ) (k k' : S.Choices) (V V' : Config G c) (p p' : Refs G f) : Prop where
  fields : Physical.Reads X A A' F F' V V' k k'
  input : Same S X W p p'
  owners : ∀ w : Site f, S.ratio.parent w∈X → (w∈d.Owners b ↔ w∈d.Owners b')

structure Care (d : AnalyticBridge.LocalGaussian.Desk G S) {R : Type*} [MeasurableSpace R]
    (l : Support c) (u : Formula G S R) : Prop where
  noted F A b k : Measurable (uncurry (u F A b k))
  comp {F F' A A' b b' k k' V V' p p'} : Survey d (ambient d l) (floor d l) F F' A A' b b' k k' V V' p p' →
    u F A b k V p=u F' A' b' k' V' p'

namespace Care
variable {R : Type*} [MeasurableSpace R] {X W Y : Support c} {u : Formula G S R}
variable (h : Care d Y u)

include h
lemma outreach {F F' A A' b b' k k' V V' p p'} (hl : ambient d Y ⊆ X) (hw : floor d Y ⊆ W)
    (H : Survey d X W F F' A A' b b' k k' V V' p p') : u F A b k V p=u F' A' b' k' V' p' :=
  h.comp ⟨Geo.Reads.mono H.fields hl,H.input.shrink hl hw,fun i hx=>H.owners i (hl hx)⟩



omit h in
lemma constant (t : R) : Care d X (fun _ _ _ _ _ _=> t) where
  noted _ _ _ _ := measurable_const
  comp _ := rfl

lemma follows {L : Type*} [MeasurableSpace L] (f : R → L) (hm : Measurable f) :
    Care d Y (fun F A b k V p=>f (u F A b k V p)) where
  noted F A b k := hm.comp (h.noted F A b k)
  comp hp := congr_arg f (h.comp hp)

omit h in
lemma together {u v : Formula G S ℝ} (hp : Care d Y u) (hq : Care d Y v) : Care d Y (fun F A b k V p=> u F A b k V p * v F A b k V p) where
  noted F A b k := (hp.noted F ..).mul (hq.noted F ..)
  comp h := congr_arg₂ HMul.hMul (hp.comp h) (hq.comp h)
end Care

variable (d : AnalyticBridge.LocalGaussian.Desk G S) (h : Route.Badge.App d)
local notation "T" => d.tube
local notation "q" => d.broadCut
local notation "x" => d.betaHat
local notation "B" => radiusB d.betaHat

abbrev aura : Formula G S (Directions G f) := fun F A b k V p => Print.shade T x q d.radius d.g A F V k p
abbrev skin : Formula G S (Config G f) := fun F A b k V p=>Print.printed T x q d.radius d.g A F V k p

-- The following are determination tests even if the occurrence is
-- disqualified later.
variable {F F' : Forest S.ratio} {A A' : Stores S} {b b' : Finset ℕ} {k k' : S.Choices}
    {V V' : Config G c} {p p' : Refs G f} {Y : Support c}
include h
lemma dress (H : Survey d (ambient d Y) (floor d Y) F F' A A' b b' k k' V V' p p') {e : Bond f}
    (h1 : portOf S e ∈ floor d Y) (h2 : S.ratio.parent (e.1+Lattice.step e.2) ∈ floor d Y) :
    aura d F A b k V p e = aura d F' A' b' k' V' p' e ∧
    skin d F A b k V p e = skin d F' A' b' k' V' p' e ∧
    (Physical.openBond A F x e ↔ Physical.openBond A' F' x e) := by
  obtain ⟨i,hi,hr⟩:=halo_spec.mp h1
  have hv : Shields (ambient d Y) (portOf S e) (18*B) := (covers_shield (40*B) hi).shift (by omega)
  have ht := h.aperture.scale
  have hz : Shields (ambient d Y) (portOf S e) 1:=hv.shrink (by omega)
  have hJ := Wires.beam_bias T x q d.radius H.fields h.aperture e hv H.input.frost
  have he := H.input.breeze e h1 h2
  have ha : Physical.openBond A F x e ↔ Physical.openBond A' F' x e := H.fields.frozen_bits ht e (hv.shrink (by omega))
  have hP : aura d F A b k V p e = aura d F' A' b' k' V' p' e := by unfold aura Print.shade; simp only [Pi.add_apply,Pi.smul_apply,hJ,he]
  refine ⟨hP,?_,ha⟩
  unfold skin Print.printed; rw [propext (Print.winter_read x H.fields e ht (hv.shrink (by omega))),
    ha,show Print.shade .. = Print.shade _ _ _ _ d.g A' F' V' k' p' e from hP, H.input.frozen hz, Wires.replica_read H.fields e hz]

omit h in
lemma floor_reach {o : Site c} (hi : o∈Y) {e : Bond f} (hx : separation o (portOf S e) ≤ 14*B) (hb : 120≤B) :
    portOf S e∈floor d Y ∧ S.ratio.parent (e.1+Lattice.step e.2)∈floor d Y := ⟨halo_spec.mpr ⟨o,hi,hx.trans (by omega)⟩,
    halo_spec.mpr ⟨o,hi,(separation_triangle _ (portOf S e) _).trans ((Nat.add_le_add hx (Work.E03.parent_step ..)).trans (by omega))⟩⟩

variable (Hc : Survey d (ambient d Y) (floor d Y) F F' A A' b b' k k' V V' p p')
include Hc
lemma daily (o : Site c) (he : o∈Y) : AgreeNear S.ratio.parent o (14*B) (skin d F A b k V p) (skin d F' A' b' k' V' p') := by
  intro e hz; obtain ⟨hi,hj⟩:=floor_reach d he (e:=e) hz h.aperture.scale
  exact (dress d h Hc hi hj).2.1
lemma ink {Z : Support f} (he : Z.image S.ratio.parent ⊆ Y) : Agrees (Z:Set (Site f)) (skin d F A b k V p) (skin d F' A' b' k' V' p') :=
  fun e hi _=>daily d h Hc _ (he (Finset.mem_image_of_mem _ hi)) _ (by rw [separation_self]; omega)
lemma oxygen (e : Bond f) (he : portOf S e∈Y) :
    p.2 e=p'.2 e ∧ (Physical.openBond A F x e↔ Physical.openBond A' F' x e) := by
  obtain ⟨h1,h2⟩ := floor_reach d he (e:=e) (by rw [separation_self]; omega) h.aperture.scale
  exact ⟨Hc.input.breeze e h1 h2,(dress d h Hc h1 h2).2.2⟩
end Voice
end YM.PhysicalNext.Dictionary
