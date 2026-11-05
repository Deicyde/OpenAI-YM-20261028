import YM.Extraction.Held
import YM.Overlay.Schedule
import YM.PCalc.Band



/-! Vertical test, through issuing books. -/
set_option autoImplicit false
noncomputable section
namespace YM.Input
open Lattice Wilson RG RG.Supply Marker Cells MeasureTheory Filter Set Function Overlay Extraction
open RG.Shoot Precision Stock
open scoped Topology Matrix.Norms.Frobenius BigOperators ENNReal ContDiff
variable {G : Gauge} {C : Sheet G} {D : Rolls C} {P : Protection D} {W : Delays P}
    {Y : Bar W} {I : Wait Y} {Z : ChartRatio G} {K : MapPrices} {Q : PostCost D} {B : Directed G I Z K Q}

/-- receipt of calibrated Primaries list. Some additional hooks may be needed
for smooth stress / rank etc in consumer packages. Doesn't merely take centered
prop; wants the actual full marker/array receipts. -/
structure Metered (F : Family G) : Prop where
  stamp : F.Makes
  enough (d : ℕ) (R : ℝ) (hr : 0<R) : ∃ T : Fuel F d R, T.ready ∧ T.covers

theorem Metered.rootwise {F : Family G} (H : Metered F) (h : G.Simple) (hk : Tabs F.path.levels) : Wcmain F := by
  refine Stops.centering ?_ H.stamp
  refine ⟨fun d R hr => ?_⟩
  obtain ⟨T,hh,hv⟩ := H.enough d R hr
  exact T.record h hk hh hv

/-- Marker horizons never inferred. Test proof uses for all periods barrier and
h functions through `Recipe.races` (both sides held), not initially taking
center estimates afresh for each position. -/
theorem bank (h : G.Simple) (hb : B.Program) (hh : Stock.Priced W)
    (hl : ∀ T, B.bake.Stays T → (B.bake.make T).Selected → ∃ F : Family G,
      F.path=B.bake.make T ∧ Metered F)
    (X : Extraction.Order) : ∃ T, ∃ (F : Family G), ∃ f S S0,
      F.path=B.bake.make T ∧ B.bake.Stays T ∧ Metered F ∧ Wcmain F ∧
      CellHyp F (X.refine f) ∧ RawLimits F (X.refine f) S S0 := by
  obtain ⟨T,hT,hO,H⟩ := B.actually h hb
  obtain ⟨F,e,k⟩ := hl T hT hO
  have ht := k.rootwise h (by rw [e]; exact Stock.consumes B.valid hh)
  have hc := Wcmain.projects F X k.stamp ht
  obtain ⟨x,p,q,w⟩ := Extraction.crops k.stamp hc
  exact ⟨T,F,x,p,q,e,hT,k,ht,Cells.recur hc.cells x,w⟩
end YM.Input
