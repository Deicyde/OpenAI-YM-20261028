import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Charges
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.ColumnCosts


/-!
# Both window conventions respond within a physical support

Here measured in output parent positions, including across the period
seam. Card check even if horizon larger than side. Genuinely coarse
L scaling, color multiplicity retained. This file concerns support of
the MATRIX and linear-coordinate shift in the Gaussian law at one held
background, NOT footprints of formulas computing entries from a background
(and answers not smooth across switches!). Full address supports and any
projector/gauge provenance other ledgers. -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianSwitch.LocalLpWindows
open Function Filter Set Matrix MeasureTheory
open Lattice Wilson RG Precision Exterior Tree Pressure Pressure.Stores Bid
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.SectorChange.Wisps Next.SectorChange.Schur
open AnalyticBridge.GaussianFieldAlignment
open FreeResolvent.Mid
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} (A : Stores S) (F : Forest S.ratio) (x : ℝ)

-- use defeq to `In x A F`. H∈ finite set coordinates
local notation "Area" => In (G:=G)
local notation "Covar" => Next.SectorChange.Gaussian.Table

def plot (p : Site c) : Finset (Area x A F) := Finset.univ.filter (fun i => separation p (front A F i) ≤ radiusB x+2)

def haloSet (X : Finset (Area x A F)) := X.biUnion (fun i => plot (G:=G) A F x (front A F i))

lemma plot_self (i : Area x A F) : i∈plot (G:=G) A F x (front A F i) := by simp [plot]
lemma halo_self (X : Finset (Area x A F)) : X ⊆ haloSet A F x X := fun i h => Finset.mem_biUnion.mpr ⟨i,h,plot_self A F x i⟩

lemma ends_inside (i j : Area x A F) (h : j∈panels A F i) : j∈plot (G:=G) A F x (front A F i) := by
  have he : meeting S x i.1.val.val j.1.val.val := h
  have hi (i : Area x A F) : front A F i ∈ Next.SectorChange.points S i.1.val.val := Set.mem_insert ..
  have hh:= he _ (hi i) _ (hi j)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩

private lemma mid_points (B : ℕ) (e d : Bond f) (h : 20*separation (axis e) (axis d) ≤ 2*S.patch.L.val*B) :
    separation (S.ratio.parent e.1) (S.ratio.parent d.1) ≤ B+2 := by
  let g := double f
  let L := S.patch.L.val
  have hP (p : Bond f) : separation (g.embed p.1) (axis p) ≤ 1 := Work.E03.sep_step ..
  have he := separation_triangle (g.embed e.1) (axis d) (g.embed d.1)
  have hh := separation_triangle (g.embed e.1) (axis e) (axis d)
  rw [upto,separation_comm (axis d) (g.embed d.1)] at he
  change 2*separation e.1 d.1 ≤ _ at he
  let q:=separation (S.ratio.parent e.1) (S.ratio.parent d.1)
  have hl := Corona.near S.ratio e.1; have hk := Corona.near S.ratio d.1
  change _ ≤ L at hl hk
  have ha := separation_triangle (S.ratio.embed (S.ratio.parent e.1)) e.1 d.1
  have hx := separation_triangle (S.ratio.embed (S.ratio.parent e.1)) d.1 (S.ratio.embed (S.ratio.parent d.1))
  rw [upto] at hx; change L*q ≤ _ at hx
  rw [separation_comm] at hl
  have ho : 3 ≤ L := S.patch.coarse
  change 20*_ ≤ 2*L*B at h
  change q ≤ B+2
  by_contra! H
  have ht := Nat.mul_le_mul_left L (show B+2 ≤ q by omega)
  have hi := hP e; have hz := hP d
  nlinarith

lemma mids_inside (i j : Area x A F) (h : j∈mids A F x i) : j∈ plot (G:=G) A F x (front A F i) := by
  have he := (Finset.mem_filter.mp (show address A F x j ∈ window S (radiusB x) (address A F x i) from h)).2
  rw [cull_address,cull_address] at he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,mid_points (S:=S) _ _ _ he⟩

-- supply actual ordered columns, no changing Gram to unmasked inverse
lemma columns_confined (Q : Covar (Area x A F)) (X : Finset (Area x A F)) :
    ColumnCosts.confined (per (panels A F) Q) (per (mids A F x) Q) X (haloSet A F x X) := by
  refine ⟨halo_self A F x X,fun i hi j hj => ?_⟩
  have hv : j ∉ plot (G:=G) A F x (front A F i) := fun he => hj (Finset.mem_biUnion.mpr ⟨i,hi,he⟩)
  exact ⟨per_zero _ _ (fun hx => hv (mids_inside A F x _ _ hx)),per_zero _ _ (fun hx => hv (ends_inside A F x _ _ hx))⟩

/-- Hybrid tables do correspond to a prescription for computing a
Gaussian with *some* actual window columns changed, on this same list
(not a new definition of `fog`). -/
def mosaicWindows (X : Finset (Area x A F)) (i : Area x A F) := if i∈X then mids A F x i else panels A F i
private lemma mosaic_calc {I : Type} [Fintype I] [DecidableEq I] (W U : I → Set I) (Q : Covar I) (X : Finset I) :
      per (fun i => if i∈X then U i else W i) Q = ColumnCosts.hybrid (per W Q) (per U Q) X := by
  ext j i
  let g (s : Set I) := per (fun _=>s) Q j i
  change g (if i∈X then U i else W i)= g (W i)+(if i∈X then g (U i)-g (W i) else 0)
  by_cases h : i∈X <;> simp [h]

lemma mosaic (Q : Covar (Area x A F)) (X : Finset (Area x A F)) :
    per (mosaicWindows A F x X) Q = ColumnCosts.hybrid (per (panels A F) Q) (per (mids A F x) Q) X :=
  mosaic_calc _ _ Q X

lemma plot_card (p : Site c) : ((plot (G:=G) A F x p).card:ℝ) ≤
    LocalJet.chips S (radiusB x+2)*(Fintype.card G.ColorIndex) := by
  let E (i : Area x A F) : Bond f × G.ColorIndex := (i.1.val.val,i.2)
  have hE : Injective E := by
    rintro ⟨⟨⟨v,hv⟩,hx⟩,i⟩ ⟨⟨⟨u,hu⟩,hz⟩,j⟩ h
    cases (Prod.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2 : (v,i)=(u,j)) -- maybe v dep
    rfl
  let W := LocalJet.members S p (radiusB x+2) ×ˢ (Finset.univ : Finset G.ColorIndex)
  have he : (plot (G:=G) A F x p).card ≤ W.card := Finset.card_le_card_of_injOn E (fun i hi => Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter (a:=i)).mp hi).2⟩,Finset.mem_univ _⟩) hE.injOn
  have ht := LocalJet.saves S p (radiusB x+2)
  refine le_trans (show ((plot (G:=G) A F x p).card:ℝ) ≤ W.card from by exact_mod_cast he) ?_
  unfold W; rw [Finset.card_product,Finset.card_univ,Nat.cast_mul]; gcongr

lemma halo_card (X : Finset (Area x A F)) : ((haloSet A F x X).card : ℝ) ≤
    X.card*(LocalJet.chips S (radiusB x+2)*(Fintype.card G.ColorIndex)) := by
  unfold haloSet
  refine le_trans (show _ ≤ ((∑ i∈X,(plot (G:=G) A F x (front A F i)).card:ℕ):ℝ) by exact_mod_cast Finset.card_biUnion_le) ?_
  push_cast; simpa using (Finset.sum_le_sum (g:=fun _ => LocalJet.chips S (radiusB x+2)*Fintype.card G.ColorIndex) (s:=X) (fun i _ => plot_card A F x (front A F i)))
end YM.SectorTools.PhysicalGaussianSwitch.LocalLpWindows
