import YM.SharpGram.Weak.Tilt
import YM.SharpGram.Weak.SubStations
import YM.OPE.Levy.Panel
import YM.SharpGram.Dense.Passes

/-!
# Complete *two-field* estimates at the calibrated weak-glass levels

TableL rows share apertures across ALL degrees ≤D here. Mixed pairs;
compare on generic points approaching the indicated (coordinate-tied)
normalization, with BOTH labels permitted to use the corresponding running
station. Keep the common subfilter untouched. Permit full offshell
price. The nonzero excesses and inverse prices below will be on a physical
basis only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Weak
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage MergeProof MergeProof.East
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Analysis Next.UVStress Climb Ward Table
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
set_option quotPrecheck false
variable {G : Gauge} {C : Family G} {Q : Table C.book} {f : Extraction.Order} (U : Final C f Q)
variable {D : ℕ} {u : Filter (ℕ×ℕ)} {H : C.Makes}
open Dense

/-- The arbitrary common `u` used here; can realize by any Ultrafilter
refinement. Eventually perspective in *k*: a close-prior index `atK` for
every large k. Same quintet down through every `d` in this horizon, which
permits mixed tests and compatible graduated bases. -/
structure Portfolio (C : Family G) (H : C.Makes) (D : ℕ) (u : Filter (ℕ×ℕ)) where
  labelsC : Binding C
  omega : HaarBudget G
  j : ChartRatio G
  p : Fin 3 → Tapes.Panel D
  z : ℝ
  named (i) : i ≤ D → MergeProof.Accent.generator G i ≤ z
  atK : ℕ → ℕ
  admits : Tendsto atK atTop atTop
  matrix : ℕ → ℕ → ℕ → TableL C D -- first index requested k (not atK), then N,p
  field : ℕ → TableL C D
  onLevel : ∀ᶠ k : ℕ in atTop,
              atK k ≤ k ∧ C.S.scale k ≤ C.S.scale (atK k)+Real.log (C.path.levels.clock.hatBeta k) ∧
              Poised p labelsC H omega j (trays D) z (atK k) (matrix k) ∧
              SubLimits C D (atK k) (p 0).arc u (matrix k) (field k)

section choose
def CanSmear (X : Portfolio C H D u) := ∃ c : ℝ, Checks (X.p 0).arc (X.p 1).arc (X.p 2).arc c (trays D) D

lemma smearsFromCoverage (hc:Coverage C H) (q : Ultrafilter (ℕ×ℕ)) (hf : (q:Filter _) ≤ f.fuse) :
    ∃ X : Portfolio C H D q, CanSmear X := by
  obtain ⟨B,O,J,K,P,c,g,hK,hp,hz,hG,hr,hY⟩ := hc.holds
  let Y k := if h:∃ Y, Poised (P D) K H O J (trays D) (c D) (g k) Y
    then h.choose else 0
  have he : ∀ᶠ k : ℕ in atTop, Poised (P D) K H O J (trays D) (c D) (g k) (Y k) :=
    (hY D).mono fun k hk => (show Y k=hk.choose from dif_pos hk) ▸ hk.choose_spec
  let T k := if h:Poised (P D) K H O J (trays D) (c D) (g k) (Y k) then (subChoices (P D 0).arc q h hf).choose else 0
  refine ⟨⟨K,O,J,P D,c D,(fun i hi => hz _ _ hi),g,hG,Y,T,?_⟩,hp D⟩
  filter_upwards [he,hr] with k hk hV
  refine ⟨hV.1,hV.2,hk,?_⟩
  unfold T; rw [dif_pos hk]; exact (subChoices (P D 0).arc q hk hf).choose_spec
lemma fromCoverage (hc:Coverage C H) (q : Ultrafilter (ℕ×ℕ)) (hf : (q:Filter _) ≤ f.fuse) :
    Nonempty (Portfolio C H D q) := ⟨(smearsFromCoverage hc q hf).choose⟩
end choose

namespace Portfolio
variable (X : Portfolio C H D u)
local notation "S" => standard C

def aperture := (X.p 0).arc
def radius (k : ℕ) := gap C.path.levels X.aperture (X.atK k)
def points (k : ℕ) := placement C.path.levels X.aperture (X.atK k)
def detector (k : ℕ) := tiltLength C.path.levels X.aperture (X.atK k)
lemma detector_rule k : detector X k=radius X k • Portfolio.points X k := tilt_rule ..
lemma charged k : 0 < radius X k := gap_pos ..
lemma detector_conf k : X.detector k ∈ conf 2 := generic_conf 2 (tilt_generic _ X.aperture (X.atK k))
lemma apertures : 0 < X.aperture := by
  unfold aperture; linarith only [(X.p 0).huge,Nat.cast_nonneg (α:=ℝ) D]
lemma detonates (h : G.Simple) : Tendsto X.radius atTop (𝓝 0) := (gap_rate _ h _).comp X.admits
variable {i : ℕ} {d e l : Fin (D+1)}
def visible (T : Table C.book)(k : ℕ)(d : Fin (D+1)) : C.label d →ₗ[ℂ] T.Field d:= (T.project d).comp (X.field k d)

variable [u.NeBot]
-- Use all arbitrary fixed label pairs. Keep STRONG budget of actual estimates.
variable (hG : G.Simple) {W r T0} (T : OPE.TableTickets C W r T0) -- Scrim
variable (hf : u ≤ f.fuse)
include X U hG T hf
open Push.FiniteDetection Push.FiniteDetection.Free
-- keep both generic higher shapes and backwardcompatible basis evaluations
lemma compareC {m : ℕ} (hm : m+1 ≤ trays D) {t : Fin (m+1) → Fin (D+1)}
    (v : (i : Fin (m+1)) → C.label (t i)) {L : Set (Points (m+1))} (hh:IsCompact L)(hz:L ⊆ conf _) :
    ∃ κ:ℝ, ∀ᶠ k:ℕ in atTop,
       let a := X.atK k; let s := (mag C.path.levels X.aperture a)⁻¹
       ∀ i : Fin (m+1) → Cover, tag s i ∈ L → tag s i ∈ generic _ →
         ‖Q.classMoment Q (fun j=> (t j).val) (tag (C.S.a a) i) (fun j => X.visible Q k (t j) (v j)) -
          (standard C).classMoment (standard C) (fun j=> (t j).val) (tag s i) (fun j => (standard C).project _ (v j))‖
             ≤ κ * Ship.budget C.path.levels (trays D) a := by
  obtain ⟨κ,hk⟩ := actualRead X.p X.labelsC H hG T.system X.omega X.j X.z X.named (0:Fin 3) v U hh hz (Nat.le_add_left ..) hm
  refine ⟨κ,?_⟩
  filter_upwards [X.onLevel,X.admits.eventually hk] with k ⟨hge,hC,hP,hZ⟩ he a s i hi hW
  exact he (X.matrix k) hP i hi hW u hf (fun j => X.field k (t j) (v j)) (fun j => hZ _ _)

lemma twoC {t : Fin 2 → Fin (D+1)} (v : (i : Fin 2) → C.label (t i)) :
    Tendsto (fun k => Q.classMoment Q (fun j=> (t j).val) (X.detector k) (fun j => X.visible Q k (t j) (v j))) atTop
      (𝓝 ((standard C).classMoment (standard C) (fun j=> (t j).val) detectors (fun j => (standard C).project _ (v j)))) := by
  obtain ⟨L,hL,hx,he⟩ := exists_compact_subset (conf_open 2) detectors_in
  obtain ⟨κ,hk⟩ := compareC U X hG T hf (m:=1) (Nat.le_add_left ..) (t:=t) v hL he -- order? check
  let A k := Q.classMoment Q (fun j=> (t j).val) (X.detector k) (fun j => X.visible Q k (t j) (v j))
  let z : Fin 2→ (standard C).Tag := jointX (d0:=fun j=>(t j).val) v
  let v k := disc z (X.points k); let y := disc z detectors
  have hs : Tendsto X.points atTop (𝓝 detectors) := (places_limit _ hG X.apertures).comp X.admits
  have hY : Tendsto v atTop (𝓝 y) := ((smoothDisc (Maxwell.table_smooth _) _).continuousOn.continuousAt ((conf_open _).mem_nhds detectors_in)).tendsto.comp hs
  change Tendsto A atTop (𝓝 y)
  have hE : Tendsto (A-v) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ (show Tendsto (fun k=>κ*Ship.budget C.path.levels (trays D) (X.atK k)) atTop (𝓝 0) from ?_)
    · filter_upwards [hk,hs.eventually (mem_nhds_iff.mpr ⟨interior L, interior_subset,isOpen_interior,hx⟩)] with k hk hx
      exact hk (strip _ X.aperture (X.atK k)) hx (placement_generic _ X.aperture (X.atK k))
    simpa only [mul_zero] using! (((Ship.diminishes _ _ hG (by unfold MergeProof.East.trays; omega)).comp X.admits).const_mul κ)
  exact (by simpa only [Pi.sub_apply,sub_add_cancel,zero_add] using! hE.add hY)
end Portfolio
end YM.SharpGram.Weak
