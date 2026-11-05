import Mathlib.RingTheory.Nilpotent.Exp
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Audition

/-!
# Interior usage certification

Separates final flag decision on the footprint from *numerical*
covariance/integral Read needs, which don't even use that one-time
flag halo. Necessary for authentic Standalone (beware that Point of
Roster may be on a sample with MORE frozen coordinates, some unused:
near the boundary of X its very type may depend on V outside X. So not
treating a list of which physical links those are as being inside X.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Arbor
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Sharp AnalyticBridge.LocalGaussian Spot AnalyticBridge.RelativeLogdet
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace YM.Push.SectorMeasure
open Wires Geo Notify Voice Voice.Check Voice.Defenses Parcel Shipment   Route SectorNext.Reconnect SectorNext.Reconnect.Words
open Finset hiding card
variable {G : Gauge} {c f : Side} {S : StepData c f} {I : Type} [DecidableEq I]
    (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art I D) (h : Lit D) (F : Forest S.ratio)
    (i : Ensign S I) (t : ℝ)
local notation "B"=>radiusB D.betaHat
local notation "X"=>wood D Z i
local notation "W"=>Route.Badge.near (Shipment.key D Z i)

def indoor := halo (55*B) (W)
local notation "Y"=>indoor D Z i

lemma patches (j) : halo (200*B) (Shipment.wind D Z j) ⊆ coat D Z j := by
  rcases j with j|j|j
  · exact Finset.Subset.trans (spread_packet (S:=S) j (by change _+500*_ ≤ 700*B; omega)) (certain _)
  · exact Finset.Subset.trans (Geo.halo_support (Finset.Subset.refl (halo (15*B) _))) (Finset.Subset.trans
      (Corona.halo_mono (by omega : 15*B+200*B ≤ 700*B) (Finset.Subset.refl _)) (shelter_K D Z _))
  exact Finset.Subset.trans (Geo.halo_support (Finset.Subset.refl (halo (15*B) _))) (Finset.Subset.trans
      (Corona.halo_mono (by omega : 15*B+200*B ≤ 700*B) (Finset.Subset.refl _)) (shelter_option D Z _))

lemma verge : halo (200*B) W⊆ X := by
  intro j hj; obtain ⟨w,hw,hr⟩:=halo_spec.mp hj; obtain ⟨z,hz,hj⟩:= Finset.mem_biUnion.mp (show w∈region (Shipment.wind D Z) i from hw)
  exact tent D Z hz <| patches D Z z (halo_spec.mpr ⟨w,hj,hr⟩)

lemma ledge (j : Site c) (ht : j∈Y) : Shields X j (12*B) := by
  intro w hw
  apply verge
  obtain ⟨z,hz,h₁⟩ := halo_spec.mp (show j∈halo (55*B) _ from ht)
  exact halo_spec.mpr ⟨z,hz,(separation_triangle z j w).trans ((Nat.add_le_add h₁ hw).trans (by omega))⟩

variable (hw : Shipment.Valid D I Z) {A A' : Stores S} {V V' : Config G c} {k k' : S.Choices} {p p' : Refs G f}
    {b : Finset ℕ}

include h hw

/-- Recheck `Shipment.printed` with bounded same Y hypotheses. -/
lemma literal (H : Physical.Reads X A A' F F V V' k k') (he : Geo.Same S Y W p p') (j) (hj : j∈i) : shutter D Z t j i F A b k V p=shutter D Z t j i F A' b k' V' p' := by
  have h0 (z : Support c) (hp : floor D z ⊆ W) : ambient D z ⊆ Y := by
    apply Corona.halo_mono (by omega) (Finset.Subset.trans (halo_subset ..) hp)
  have hh z (hp : floor D z ⊆ W) : Survey D (ambient D z) (floor D z) F F A A' b b k k' V V' p p' :=
    ⟨Geo.Reads.mono H (Finset.Subset.trans (h0 z hp) (fun i hi=> (ledge D Z _ _ hi).center)), he.shrink (h0 z hp) hp, fun _ _=>Iff.rfl⟩
  have ht := needing D Z hj
  have hu := Shipment.tent D Z hj
  rcases j with j|j|j
  · unfold shutter Booklet.vitalPage
    dsimp only
    obtain ⟨hq,hp⟩:=Booklet.same_ledger D Z h.toApp j H hu
    rw [hq,hp]
    apply congr_arg Complex.ofReal
    refine congr_arg₂ HMul.hMul (Finset.prod_congr rfl fun x hx=>?_) (congr_arg Real.exp (Finset.sum_congr rfl fun x hx=>?_))
    · have hv := (Shipment.packet_test D Z h.aperture.scale ((Finset.mem_filter.mp hx).2.2)).2
      exact (Check.film D h.toApp x).comp (hh _ (hv.trans ht))
    have hv := (Shipment.packet_log D Z h.aperture.scale ((Finset.mem_filter.mp hx).2.2)).2
    exact (local_series D h.toApp x).comp (hh _ (hv.trans ht))
  · exact (basics D Z h hw j _).2.1.comp (hh _ ht)
  have ho₁ {O} (h : O⊆sights D Z j) := hh O ((Corona.halo_mono (a:=15*B) le_rfl h).trans ht)
  have ho₂ O (h : O⊆sights D Z j) : halo (700*B) O⊆ X := (Corona.halo_mono le_rfl h).trans ((shelter_option D Z j).trans hu)
  rcases j with j|⟨j,u⟩|(j|⟨j,u⟩)|j
  · let z := ho₁ (Finset.Subset.refl (post S j))
    unfold shutter choices; dsimp only; rw [(Check.film D h.toApp j).comp z,(tarp_care D h.toApp (post S j)).comp z]
  · let z:=ho₁ (show Voice.native D j ⊆ _ from Finset.subset_union_left)
    unfold shutter choices shine; dsimp only
    rw [(guarded D h.toApp j).comp z]; cases j with
    | letter l=> dsimp only; rw [tip_read h.toApp l t (not_congr (record_at H _ (600*B) le_rfl h.aperture.scale (ho₂ _ Finset.subset_union_left))) z]
    | _=>rfl
  · rfl
  · let z:=ho₁ (show sourceSites D Z j⊆ _ from Finset.subset_union_left)
    have hx : remote D (sourceSites D Z j) A ↔ remote D (sourceSites D Z j) A' := not_congr (record_at H _ (600*B) le_rfl h.aperture.scale (ho₂ _ Finset.subset_union_left))
    have hp : Z.score j (skin D F A b k V p)=Z.score j (skin D F A' b k' V' p') := (basics D Z h hw j none).1.comp z
    unfold shutter choices; dsimp only
    rw [((basics D Z h hw j none).2.2).comp z]; unfold Shipment.surge; dsimp only; rw [(gamma_care h.toApp _ t).comp z,
      (tarp_care D h.toApp _).comp z,hp]; simp only [hx]
  rfl

lemma across (H : Physical.Reads X A A' F F V V' k k') (he : Geo.Same S Y W p p') : (∏ j∈i, shutter D Z t j i F A (SectorNext.Reconnect.Fleet.kSet i) k V p) =
    ∏ j∈i,shutter D Z t j i F A' (SectorNext.Reconnect.Fleet.kSet i) k' V' p' :=
    Finset.prod_congr rfl fun j hj=> literal D Z h F i t hw H he j hj
end YM.PhysicalNext.Dictionary.Arbor
