import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Postage
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Voice

/-! Before any gates are dropped. Patch every candidate regular link
in this footprint, not only those with nonzero realized coefficients.
Chill-stable lookup on the support. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Voice
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Wires Geo Notify Print
variable {G : Gauge} {c f : Side} {S : StepData c f} (d : AnalyticBridge.LocalGaussian.Desk G S) (h : Route.Badge.App d)
local notation "T" => d.tube
local notation "q" => d.broadCut
local notation "x" => d.betaHat
local notation "B" => radiusB d.betaHat

def zone (l : Support c) : Finset (Bond f) := Finset.univ.filter fun e=>portOf S e ∈ floor d l ∧
    S.ratio.parent (e.1+Lattice.step e.2)∈ floor d l


def tarp (l : Support c) : Formula G S ℝ := fun F A b k V p =>
    ∏ i∈zone d l, if Physical.openBond A F x i then broad q (2*d.radius) (aura d F A b k V p i) else 1
include h
lemma tarp_care (l : Support c) : Care d l (tarp d l) := by
  constructor
  · intro F A b k
    unfold tarp uncurry
    obtain ⟨P,hP⟩:=h.valid.funds
    refine Finset.measurable_fun_prod _ fun j hj=>?_; split
    · exact (broad_smooth q (2*d.radius)).continuous.measurable.comp
        (shade_meas T x q d.radius d.g hP k A F h.valid.positive h.enough j)
    exact measurable_const
  intro F F' A A' b b' k k' V V' p p' hj
  refine Finset.prod_congr rfl fun i hi=>?_
  have ht := (Finset.mem_filter.mp hi).2
  have hx := dress d h hj ht.1 ht.2
  rw [hx.2.2,hx.1]

omit h in
lemma affordable (l : Support c) {F A b k V p} : tarp d l F A b k V p∈Set.Icc (0:ℝ) 1 := by
  have he (i : Bond f) : (if Physical.openBond A F x i then broad q (2*d.radius) (aura d F A b k V p i) else 1) ∈ Set.Icc (0:ℝ) 1 := by
    split
    · exact broad_range ..
    exact ⟨zero_le_one,le_rfl⟩
  exact ⟨Finset.prod_nonneg fun i _ => (he i).1,(Finset.prod_le_prod (fun i _=> (he i).1) (fun i _=>(he i).2)).trans (by simp)⟩

namespace Spotter
variable (F : Forest S.ratio) (k₀ : S.Choices) (A : Stores S) (k : S.Choices) (b : Finset ℕ)
    (V : Config G c) (hc : Spot.Clearing (chosen d F k₀ A k) V)
include hc
local notation "u" => chosen d F k₀ A k
theorem protects (p : Geo.Refs G f)
    (H : ∀ i : (u).ActiveKey, (u).gate b (.inl (.inr (.inr (.inr (.inr i))))) V (Print.see x A F p) ≠ 0)
    (l : Support c) : tarp d l F A b k V p=1 := by
  refine Finset.prod_eq_one fun i hi=>?_
  split
  next he =>
    obtain ⟨j,rfl⟩ := he
    obtain ⟨_,hj⟩:=h.earns A F V hc.flags
    obtain ⟨η,hη,hg⟩:=h.gaps A F V k hc.flags
    have ht := H j
    refine broad_one q (by linarith [h.valid.positive] : 0<2*d.radius) ?_
    unfold aura
    rw [Print.tinting T x q d.radius d.g k j V h.aperture hj hη hg p]
    exact (broad_span q h.valid.positive _ ht).le
  rfl
end Spotter


end YM.PhysicalNext.Dictionary.Voice
