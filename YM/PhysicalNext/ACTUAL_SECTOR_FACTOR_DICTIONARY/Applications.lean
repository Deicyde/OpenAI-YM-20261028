import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Alabaster
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Estimate
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Voice

/-! One row of the affine debit. Use surrogate only even for the
standalone formula touching a different sector's mask; must agree with
the true row *with its selection predicate* in exact spelling. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace

namespace Voice
open Wires Geo 
variable {G : Gauge} {c f : Side} {S : StepData c f} (d : AnalyticBridge.LocalGaussian.Desk G S)
local notation "T" => d.tube
local notation "q" => d.broadCut
local notation "x" => d.betaHat
local notation "B" => radiusB d.betaHat

-- use rate=0 for m only, d.g for residualDebit
def arrow (rate : ℝ) (F : Forest S.ratio) (A : Stores S) (k : S.Choices) (V : Config G c) (p : Refs G f) : Directions G f := fun i=>
    broken x q d.radius V p.1 A F i + if Physical.openBond A F x i then Print.shade T x q d.radius rate A F V k p i else 0

def debit (rate : ℝ) (i : Slots S) : Formula G S ℝ := fun F A b k V p =>
    if keep x (shots S x) A F i then ‖tRow T x V k A F (arrow d rate F A k V p) i‖^2/2 else 0

theorem dispatch (h : Route.Badge.App d) (rate : ℝ) (i : Slots S) : Care d {spot S i} (debit d rate i) := by
  obtain ⟨P,hP⟩ := h.valid.funds
  constructor
  · intro F A b k
    let f₁ (y : Config G c × Refs G f) := arrow d rate F A k y.1 y.2
    have hf : Measurable f₁ := by
      have hl : Measurable (fun y : Config G c × Refs G f => broken x q d.radius y.1 y.2.1 A F) := (broken_meas x q d.radius A F h.valid.positive h.enough).comp (f:=fun (y : Config G c × Refs G f) => (y.1,y.2.1))
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      refine measurable_pi_lambda _ fun j=> Measurable.add ((measurable_pi_apply j).comp hl) ?_
      split
      · exact Print.shade_meas T x q d.radius rate hP k A F h.valid.positive h.enough j
      exact measurable_const
    have he := (FieldJet.bump'_meas T x h.aperture.branched k i).comp (measurable_fst.prodMk hf)
    have hl : Measurable (fun y : Config G c × Refs G f=> base T x y.1 k i) := (Fabric.core hP x k i).comp measurable_fst
    unfold uncurry debit; split
    · exact ((hl.add he).norm.pow_const 2).div_const _
    exact measurable_const
  intro F F' A A' b b' k k' V V' p p' H
  have ht : Shields (ambient d {spot S i}) (spot S i) (40*B) := covers_shield _ (Finset.mem_singleton_self _)
  have hB := h.aperture.scale
  have hv : Shields (ambient d {spot S i}) (spot S i) (4*B+1) := ht.shrink (by omega)
  have hL := (drawn T x k k' V V' h.aperture i (Geo.Reads.visit H.fields hv) (Geo.Reads.way H.fields hv)).1
  have hF (j : Bond f) (hj : separation (spot S i) (portOf S j) ≤ B) := ht.shift (show _ + 18*B ≤ 40*B by
    exact Nat.add_le_add_right hj _ |>.trans (by omega))
  have hz := FieldJet.around T x (arrow d rate F A k V p) (arrow d rate F' A' k' V' p') i h.aperture
    (Geo.Reads.visit H.fields hv) (Geo.Reads.way H.fields hv) (fun j (hj : separation (spot S i) _ ≤ B) => ?_)
  swap
  · have he := hF j hj
    have hp : Shields (floor d {spot S i}) (portOf S j) 1 :=
      (covers_shield _ (X:=_) (Finset.mem_singleton_self _)).shift (by change _+1≤15*B; omega)
    unfold arrow
    rw [Wires.broken_read x q d.radius H.fields j H.input.frost hB (he.shrink (by omega)),
      H.fields.frozen_bits hB j (he.shrink (by omega)), Print.shade_read T x q d.radius rate H.fields h.aperture j he hp H.input]
  unfold debit tRow; rw [Wires.participates _ H.fields hB h.aperture.spans i (ht.shrink (by omega)), hL,hz]

section genuine
variable {A : Stores S} {F : Forest S.ratio} (h : Route.Badge.App d) (k : S.Choices) (V : Config G c)
    (hv : A.flags=RG.flags (temp d.betaHat) V) (p : Geo.Refs G f) (r : ℝ)
include h hv

-- preserves displacement for each active input; even when using the
-- portal at r=0, don't substitute a recomputed no-hole precision
lemma given :
    let u := Print.see x A F p
    arrow d r F A k V p = input x A F (autoShell q d.radius V u.1) + fresh x (shots S x) A F
      (displaced (meanLog A F T x V k q d.radius u.1) r u.2) := by
  intro u
  obtain ⟨_,ht⟩ := h.earns A F V hv
  obtain ⟨η,hη,hg⟩ := h.gaps A F V k hv
  funext i
  unfold arrow broken; rw [Pi.add_apply]
  refine congr_arg₂ HAdd.hAdd rfl ?_
  unfold fresh; by_cases he : i∉F.trunks
  · rw [dif_pos he]
    let j : F.Free := ⟨i,he⟩
    by_cases hh : ¬chill A x F ⟨i,he⟩
    · rw [dif_pos hh]
      let z : Active A x F := ⟨j,hh⟩
      rw [if_pos (show Physical.openBond A F x i from ⟨z,rfl⟩)]
      exact Print.tinting T x q d.radius r k z V h.aperture ht hη hg p
    · rw [dif_neg hh, if_neg (by intro hu; exact hh ((Print.sees_breeze x A F j).mp hu))]
  · rw [dif_neg he, if_neg (fun hh => he ((Physical.mask A F x i).mp hh).1)]

lemma debits (i : Slots S) (b : Finset ℕ) :
    let u := Print.see x A F p
    debit d r i F A b k V p = if keep x (shots S x) A F i then
        ‖lands T x V k (shots S x) A F q d.radius u.1 (meanLog A F T x V k q d.radius u.1+r • u.2) i‖^2/2 else 0 := by
  intro u
  unfold debit tRow; split
  next he =>
    obtain ⟨_,ha⟩:= h.earns A F _ hv
    rw [FieldJet.agrees _ _ _ _ ha _ _ he,given d h k V hv p r]; rfl
  rfl
end genuine
end Voice
end YM.PhysicalNext.Dictionary
