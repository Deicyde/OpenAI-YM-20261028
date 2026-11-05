import YM.AnalyticBridge.RESET_INCOME_PORT.Plate
import YM.Next.UV_STRESS.Across
import YM.Next.UV_STRESS.Fringe
import YM.Push.COMMON_WITNESSES.Link
import YM.UVNext.COUPLING_RESET.Precision


set_option warningAsError false

/-!
# Actual linkwise log-J forecast for the Income price

Work with the actual ChartRatio on that Directed. Keep charge before
threshold of Remaining holds. Predict by the first three multilinear
terms inside each broad guard; use even where logGuard is an extension.
No claim about the Jacobian of evaluating or exposing a path on the
affine *shifted* array with V varying; purely at observed plate coordinates.
Gives an order zero per-link O(d³), separately meeting the price/purchase
order (O(d²) would not be the `funds` ticket).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome.Sheen

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open Metric FormalMultilinearSeries UVNext.CouplingReset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge}

structure Gloss (Z : ChartRatio G) where
  films : FormalMultilinearSeries ℝ G.Color ℝ
  localChart : LocalRatio Z
  ready : HasFPowerSeriesAt (fun y : G.Color => Real.log (Z.J y)) films 0
  cents : ℝ
  zone : ℝ
  cash : 0<cents
  hp : 0<zone
  spatial : zone < Z.radius
  knows (x : G.Color) : ‖x‖ ≤ zone → |Real.log (Z.J x)-films.partialSum 3 x| ≤ cents*‖x‖^3



variable {Z : ChartRatio G}









def bloom {c f : Side} {S : StepData c f} (e : Plate G S) (H : Gloss e.chart) (A : Stores S) :=
    (Fintype.card (Active A e.x e.forest) : ℝ) * (H.cents*(4*e.d)^3)

/-- The bore price fits a reserve at arbitrary accuracy at fixed-L, even
post transition stagger, even all periods. Not inferred retroactively
unless the gate was in the delays. -/
lemma luster (L : Side) (E : Gloss Z) (σ w : ℝ) (hσ : 0<σ) (hw : 0<w) : ∀ᶠ x : ℝ in atTop,
    let d := w * fiery G x L
    0<d ∧ 4*d ≤ E.zone ∧ ∀ {c f : Side} (S : StepData c f), S.patch.L=L →
      ∀ (F : Forest S.ratio) (A : Stores S), (Fintype.card (Active A x F):ℝ)*(E.cents*(4*d)^3) ≤
        sites c*(σ * Vac.Numbers.Hat x^((11:ℝ)/5)) := by
  let v := G.slopeConstant * Real.log L.val
  let n : ℝ := Fintype.card Axis * (L.val:ℝ)^4
  have hn : 0≤n := by unfold n; positivity
  let c := n * E.cents * (4*w*2)^3 / σ
  have h : ∀ᶠ x : ℝ in atTop, temp (x+v) / temp x ≤ 2 := (Work.E09.temp_ratio v).eventually (ge_mem_nhds
    (by norm_num : (1:ℝ)<2))
  filter_upwards [h, Work.E01.fiery_le G L (4*w), (Work.E09.betaF_growth G L).eventually (eventually_gt_atTop 0),
    (Work.E01.largeT_tendsto G L).eventually (ge_mem_nhds E.hp),eventually_gt_atTop (1:ℝ),late_cubic c]
    with x hx hv hy hz hp hC
  have hh : 0<fiery G x L := Work.E09.temp_pos hy
  have ht := Work.E09.temp_pos (show 0<x by linarith)
  intro d; refine ⟨mul_pos hw hh,by unfold d; linarith only [hv,hz],?_⟩
  intro c' f S hL F A
  have hK : Fintype.card (Active A x F) ≤ Fintype.card (Site f) * Fintype.card Axis := by
    refine (Fintype.card_le_of_injective _ (Subtype.val_injective (p:=fun i : F.Free => ¬chill A x F i))).trans
      ((Fintype.card_le_of_injective _ (Subtype.val_injective (p:=fun i : Bond f=>i∉F.trunks))).trans_eq ?_)
    exact Fintype.card_prod ..
  have hr : (Fintype.card (Active A x F):ℝ) ≤ sites c'*n := by
    unfold sites n
    norm_cast; refine hK.trans_eq ?_
    rw [site_card,site_card,S.sizes,hL]; simp; ring
  have ht' : fiery G x L ≤ 2*temp x := (div_le_iff₀ ht).mp hx
  change c * temp x ^ 3 ≤ _ at hC
  refine (mul_le_mul_of_nonneg_right hr (by have := E.cash; unfold d; positivity)).trans ?_
  rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (sites_pos _).le
  unfold c at hC; rw [div_mul_eq_mul_div,div_le_iff₀ hσ] at hC
  unfold d; apply le_trans (b:=n* (E.cents * (4*(w*(2*temp x)))^3)) ?_ ?_
  · have := E.cash; gcongr
  nlinarith only [hC]
end YM.AnalyticBridge.ResetIncome.Sheen
