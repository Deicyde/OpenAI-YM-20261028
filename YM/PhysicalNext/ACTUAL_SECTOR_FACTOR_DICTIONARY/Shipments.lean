import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Order

/-! Raw physical addresses, compatibility & query margins. We use a
K-placeholder telling packet & q eligibility/address suppression and,
optional on the same stencil, a qualifier address telling which
polynomial alternative at that K (absence ⇒ vacuum alternative). Its
support forces these two addresses into the SAME component. No division
by K (which may of course be zero while its marked alternative is nonzero).

The finite marker interface just names the primitive amplitudes &
placements of the hypotheses on the *incoming density*. Instantiate from
Overlay bands (and sleep it entirely for unmarked). Origins invariant
before projection. This is a pointwise untruncated dictionary; pass to
surviving marker monomials only, allowing arbitrary monomial *value*
zeroing in the input for excluded ones (not altering vacuum letter
organization). Do NOT infer unmarked estimates for such marker terms.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace

namespace Shipment
open Wires Geo Notify Voice Voice.Check Parcel SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
variable (I : Type*) -- actual markers

/-- All on one incoming dictionary incl zero histories. -/
structure Art (I : Type*) (D : AnalyticBridge.LocalGaussian.Desk G S) where
  origin : I → Site f
  names : ℕ → Finset I -- bulk marker alternative with its support
  plot : ℕ → Support f
  sig : ℕ → ℕ → Finset I -- K slot & variant
  units : I → ℂ
  score : ℕ → Config G f → ℂ -- pre regular mask
  essay : ℕ → ℕ → Config G f → ℂ -- K variant

-- primitive input premises as in WM. A zero-address forced padding variant
-- is allowed to omit the corresponding anchors in the forced address content
-- (Overlay interface); in that case still include them in its raw auxiliary
-- support. K itself still uses forced.support NOT that enlargement.
structure Valid (Z : Art I D) : Prop where
  located i x : x∈ Z.names i → Z.origin x∈Z.plot i
  registered i : Z.names i = ∅ → Z.score i=0
  bulk i : D.input.p.Regular (Z.plot i) (Z.score i)
  frank i j : Z.sig i j = ∅ → Z.essay i j=0
  orders i j x : Z.essay i j≠0 → x∈Z.sig i j → Z.origin x∈ (D.labels.forced i).support
  forced i j : UsesFinal D.input.p.threshold (D.labels.forced i).support (Z.essay i j)
  meas i j : Measurable (Z.essay i j)
  invariant i j : GaugeInvariant (Z.essay i j)
  heads i j U : Z.essay i j U ≠ 0 → (D.labels.forced i).eligible D.input.p.threshold U

abbrev Bills (S : StepData c f) (I : Type) := Voice.Check.Test c f ⊕ ((ListID S × Bool) ⊕ ((I ⊕ ℕ × Bool) ⊕ ℕ × ℕ))
abbrev Bill (S : StepData c f) (I : Type) := Fleet.Label c f (Bills S I)
abbrev Subject (S : StepData c f) (I : Type) := Voice.Check.Test c f ⊕ ListID S ⊕ ((I ⊕ ℕ) ⊕ ℕ)

section names
variable {ι : Type}
abbrev pack (p : Fleet.Packet c f) : Bill S ι := Sum.inl p
abbrev known (a : ℕ) : Bill S ι := Sum.inr (.inl a)
abbrev suggest (i : Bills S ι) : Bill S ι := Sum.inr (.inr i)
abbrev supplement (i : Voice.Check.Test c f) : Bills S ι := Sum.inl i
abbrev accent (i : ListID S) (b : Bool) : Bills S ι := Sum.inr (.inl (i,b))
abbrev singleton (i : ι) : Bills S ι := Sum.inr (.inr (.inl (.inl i)))
abbrev bead (i : ℕ) (b : Bool) : Bills S ι := Sum.inr (.inr (.inl (.inr (i,b))))
abbrev qualify (i j : ℕ) : Bills S ι := Sum.inr (.inr (.inr (i,j)))

def question : Bills S ι → Subject S ι
  | .inl i=>Sum.inl i
  | .inr (.inl i)=>Sum.inr (.inl i.1)
  | .inr (.inr (.inl (.inl i)))=>Sum.inr (.inr (.inl (.inl i)))
  | .inr (.inr (.inl (.inr i)))=>Sum.inr (.inr (.inl (.inr i.1)))
  | .inr (.inr (.inr i))=>Sum.inr (.inr (.inr i.1)) -- K variant, binder by slot

variable [DecidableEq ι] (Z : Art ι D)

def burns : Bills S ι → Finset ι
  | .inl _ | .inr (.inl _) => ∅
  | .inr (.inr (.inl (.inl i)))=> {i}
  | .inr (.inr (.inl (.inr i)))=> Z.names i.1
  | .inr (.inr (.inr i))=> Z.sig i.1 i.2

def burst : Bill S ι → Finset ι := Sum.elim (fun _=>∅) (Sum.elim (fun _=>∅) (burns D Z))

def pole (i : ι) : Site c := S.ratio.parent (Z.origin i)

def logSites (i : ListID S) := Voice.native D i ∪ ask D i

def sourceSites (i : ℕ) : Support c := (inspected (Z.plot i)).image S.ratio.parent
-- for a zero dummy alternative, pad to nonempty sets with the origin at
-- the very end (not to declare reads). Also add any marker posts for the degenerate
-- forced variant; if nonzero they are included anyway by Valid & Halo.
def sights (i : Bills S ι) : Support c := match i with
  | .inl i => post S i
  | .inr (.inl i)=>logSites D i.1
  | .inr (.inr (.inl (.inl i))) => {pole D Z i}
  | .inr (.inr (.inl (.inr i))) => sourceSites D Z i.1 ∪ (Z.names i.1).image (pole D Z)
  | .inr (.inr (.inr i)) => custody D i.1 ∪ (Z.sig i.1 i.2).image (pole D Z)

local notation "B" => radiusB D.betaHat

def wind (i : Bill S ι) : Support c := match i with
  | .inl i => region (Fleet.spans S (500*B)) i
  | .inr (.inl i)=> floor D (custody D i)
  | .inr (.inr i)=> floor D (sights D Z i)

def insure (X : Support c) := if X.Nonempty then X else {0}
lemma certain (X : Support c) : X ⊆ insure X := by unfold insure; split; rfl; rename_i hh; simp [Finset.not_nonempty_iff_eq_empty.mp hh]
lemma lives (X : Support c) : (insure X).Nonempty := by unfold insure; split; assumption; simp

def coat (i : Bill S ι) : Support c := insure <| match i with
  | .inl i=>region (Fleet.spans S (hump B)) i
  | .inr (.inl i)=>halo (700*B) (custody D i)
  | .inr (.inr i)=>halo (700*B) (sights D Z i)

-- Held patch demand: for packet's hard U through 300 (& logs used at
-- inner rows), we can even hold *all* the links through 400, charged
-- by the preserved broad doors (both endpoint checks).
def handling (i : Bill S ι) : Finset (Bond f) := match i with
  | .inl P=> Finset.univ.filter fun e=>portOf S e∈region (Fleet.spans S (400*B)) P
  | .inr (.inl i)=>zone D (custody D i)
  | .inr (.inr i)=> match i with
    | .inl j=> if bare j then zone D (post S j) else ∅
    | .inr (.inl j)=> if Voice.Defenses.curtain j.1 then zone D (Voice.native D j.1) else ∅
    | .inr (.inr (.inl (.inr j)))=>zone D (sourceSites D Z j.1)
    | _=>∅
end names

section prices
variable {ι : Type} [DecidableEq ι] (Z : Art ι D)
local notation "B" => radiusB D.betaHat

lemma coat_full (i : Bill S ι) : (coat D Z i).Nonempty := lives _

private lemma expand {a b m z : ℕ} {X : Support c} (he : m+a ≤ b) : halo (m*z) (halo (a*z) X) ⊆ insure (halo (b*z) X) :=
  Finset.Subset.trans (Geo.halo_over ..) (Finset.Subset.trans (Corona.halo_mono (by rw [← Nat.add_mul]; gcongr) (Finset.Subset.refl _))
    (certain ..))

lemma spread_packet (P : Fleet.Packet c f) {u v a : ℕ} (h : a+u ≤ v) :
    halo a (region (Fleet.spans S u) P) ⊆ region (Fleet.spans S v) P := by
  intro i hi
  obtain ⟨t,ht,hr⟩:=halo_spec.mp hi
  obtain ⟨j,hj,hU⟩:=Finset.mem_biUnion.mp ht
  obtain ⟨w,hw,hy⟩:=halo_spec.mp hU
  exact Finset.mem_biUnion.mpr ⟨j,hj,halo_spec.mpr ⟨w,hw,(separation_triangle w t i).trans (by omega)⟩⟩

lemma wind_sewn (i : Bill S ι) : halo (20*B) (wind D Z i) ⊆ coat D Z i := by
  rcases i with i|i|i
  · exact Finset.Subset.trans (spread_packet (S:=S) i (by change 20*_+500*_≤700*B; omega)) (certain _)
  · exact expand (by omega : 20+15≤700)
  exact expand (by omega : 20+15≤700)

lemma sources_touched (i : Bills S ι) (t : ι) (ht : t∈burns D Z i) : pole D Z t ∈ sights D Z i := by
  rcases i with i|i|(i|j)|j <;> simp only [burns,sights] at ht ⊢ <;>
    first | exact (Finset.notMem_empty _ ht).elim | rw [Finset.mem_singleton.mp ht]; exact Finset.mem_singleton_self .. |
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)

lemma owner_reserve (i : Bill S ι) (t) (ht : t∈burst D Z i) : pole D Z t∈coat D Z i := by
  rcases i with i|i|i
  · exact False.elim (Finset.notMem_empty _ ht)
  · exact False.elim (Finset.notMem_empty _ ht)
  exact certain _ (halo_subset _ _ (sources_touched D Z i t ht))

end prices
end Shipment
end YM.PhysicalNext.Dictionary
