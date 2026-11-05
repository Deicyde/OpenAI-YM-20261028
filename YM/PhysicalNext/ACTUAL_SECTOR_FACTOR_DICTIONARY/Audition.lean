import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Sources

/-!
# Compatible completion

Every raw label now sees the real sector & one integration field at its
retained footprint. Keep also nonconnected, empty and otherwise dead
addresses allocated as ZERO (no artificial empty polymer). Don't pad
an incompatible component measure by an identity prescription.
-/
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
    (F : Forest S.ratio) (k₀ : S.Choices) (V : Config G c)
local notation "B"=>radiusB D.betaHat
local notation "t₀"=>D.betaHat

abbrev Ensign (S : StepData c f) (ι : Type) := Finset (Bill S ι)
instance [Countable ι] : Countable (Ensign S ι) := by
  letI : Countable (Bills S ι) := inferInstance
  letI : Countable (Bill S ι) := inferInstance
  unfold Ensign; infer_instance

def wood (i : Ensign S ι) := insure (region (coat D Z) i)
def signal (s : Ensign S ι) := s.biUnion (burst D Z)

def stars : Almanac D.tube D.allocation D.input F where
  point:= D.out
  H := Native.kinetic D.tube F k₀ t₀
  J := D.chart
  d := D.radius
  q := D.broadCut
  list _ := shots S t₀
  C A V k:=fog A F D.tube t₀ V k
  m A V k:=meanLog A F D.tube t₀ V k D.broadCut D.radius

lemma flames (s : Ensign S ι) (r : ℕ) : (Shipment.station s).dome r=s.biUnion
    (fun i=> (region (Fleet.spans S r) (Fleet.useSeeds i))) := by
  rw [Shipment.station,stocked]; ext i
  simp only [Fleet.events, region, Finset.mem_biUnion]; grind

lemma tent {i : Ensign S ι} {j} (h : j∈i) : coat D Z j ⊆ wood D Z i := fun x hx=> certain _ (Finset.mem_biUnion.mpr ⟨j,h,hx⟩)

lemma prices (i : Ensign S ι) {r} (h : r≤hump B) : (Shipment.station i).dome r ⊆ wood D Z i := by
  intro j hj; rw [flames] at hj
  obtain ⟨a,ha,hl⟩ := Finset.mem_biUnion.mp hj; rcases a with a|a
  · have he := spread_packet (S:=S) a (a:=0) (show 0+r ≤ hump B by omega) (halo_subset 0 _
      (show j∈region (Fleet.spans S r) a from hl))
    exact tent D Z ha (shelter_packet D Z a he)
  change j∈region (Fleet.spans S r) ∅ at hl; simp [region] at hl

def icons : Cards S (Ensign S ι) ι where
  X:=wood D Z
  full i := Shipment.lives _
  posts:= Shipment.pole D Z
  seeds:= Shipment.station
  gate i := fun x hx=> prices D Z i (Nat.zero_le _) (halo_subset 0 _ hx)
  marks:=Shipment.signal D Z
  around i e he := by
    obtain ⟨a,ha,hx⟩:=Finset.mem_biUnion.mp he
    exact tent D Z ha (owner_reserve D Z a e hx)

def key (i : Ensign S ι) : Route.Badge S t₀ (wood D Z i) where
  near:=region (wind D Z) i
  held:=i.biUnion (handling D Z)
  sewn := by
    intro w hw; obtain ⟨z,hz,hq⟩:=halo_spec.mp hw; obtain ⟨a,ha,ht⟩:=Finset.mem_biUnion.mp hz
    exact tent D Z ha (wind_sewn D Z a (halo_spec.mpr ⟨z,ht,hq⟩))

lemma needing {i : Ensign S ι} {j} (h : j∈i) : wind D Z j⊆(key D Z i).near := fun x hx=>Finset.mem_biUnion.mpr ⟨j,h,hx⟩

lemma nearby (i : Ensign S ι) : Route.Localized t₀ (icons D Z) i := ⟨prices D Z i (by unfold hump; omega)⟩

/-- actual fixed tag-law roster. -/
def theater : Roster (stars D F k₀) V (icons D Z) :=
    Route.clears (nearby D Z) (key D Z) V F h.aperture.scale h.aperture.branched h.aperture.spans (fun _ _ _=>rfl)
-- page is same shape even off V neighborhood (but i representative
-- patch chosen with completed V flags).

def privilege (i : Ensign S ι) := Ac.Spark (coat D Z) i ∧ permits (requirement D Z F) i ∧
    wood D Z i ∩ RG.flags (temp t₀) V=(Shipment.station i).flags

abbrev play (i : Ensign S ι) := theater D Z h F k₀ V |>.sample i
abbrev ScriptC := (i : Ensign S ι) → S.Choices → ((theater D Z h F k₀ V).point i)→ℂ

def lines : ScriptC D Z h F k₀ V := fun i k T => if privilege D Z F V i then
    ∏ j∈i, shutter D Z t j i F (play D Z h F k₀ V i) (Fleet.kSet i) k V ((key D Z i).embroider T) else 0

include HZ
lemma ensemble {i : Ensign S ι} (k : S.Choices) : Measurable (lines D Z t h F k₀ V i k) := by
  unfold lines; split
  next hv=>
    let A := play D Z h F k₀ V i
    let f (j : Bill S ι) := shutter D Z t j i F A (Fleet.kSet i) k
    let m := (key D Z i).embroider (F:=F) (O:=A) (G:=G)
    have he (j) : Measurable (uncurry (f j)) := shutter_meas D Z t h HZ j i ..
    exact Finset.measurable_fun_prod _ (fun j _=> (he j).comp (f:=fun p=>(V,m p)) (measurable_const.prodMk ((key D Z i).embroider_meas)))
  exact measurable_const


end YM.PhysicalNext.Dictionary.Shipment
