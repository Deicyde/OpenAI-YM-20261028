import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.DriftB
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.MakeB

/-!
# Sector products measure on all Y,Z

No assertion of integrability from measurable. Stencils cohere through
global reader `X.wrapY`. Later smallness on calibrated data gives norms of
actual integrated cells.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ x : ℝ} (X : Coat T F)
variable {α : Type*} [MeasurableSpace α] {Y : α→F.Slice G} (hY : Measurable Y)
variable (hc : ShellAccess S G X.x W X.width γ)

section masks
include hY
lemma paidK {U : α→Directions G f} (hU : Measurable U) (p : ℕ) {R : Rep G f} (h : Intake P T X.x R)
    (a : ℝ) : Measurable (fun v => (X.wrapY (Y v)).bag R a (U v) p) := by
  have hP := X.enforce_b (2*a) (X.plaza (Raw.forcedFoot S.ratio 0 X.B R p))
  exact ((h.cap.labels.forced.meas p).comp (X.summon hY hU)).mul (hP.comp hU)
lemma charged_b {U : α→Directions G f} (hU : Measurable U) (p : Panic c f) (l : Finset ℕ) (R : Rep G f) (A : Stores S)
    (W : ℝ) (h : P.Funds S T) : Measurable (fun v => (X.wrapY (Y v)).rawStorm (U v) W A R l p) := by
  have hf := X.summon hY hU
  rcases p with p|p|p|p|p
  · exact (X.fine_b p A).comp hf
  · exact (X.bond_b p A h (W:=W)).comp hf
  · exact (pin_b p X.k h).comp hf
  · exact (site_b p X.k (G:=G)).comp hf
  exact (contract_b p l R).comp hf
lemma det_b {U : α→Directions G f} (hU : Measurable U) (i : WarningAt c f) (l : Finset ℕ) (R : Rep G f)
    (W a : ℝ) (h : P.Funds S T) : Measurable (fun v => (X.wrapY (Y v)).detect (U v) W a R l i) := by
  rcases i with i|i
  · let Z := X.plaza (halo X.B (districts S i))
    change Measurable (fun v => if mandatory X.seeds X.B i then 0 else X.enforce (2*a) (U v) Z*
      ((X.wrapY (Y v)).rawStorm (U v) W X.seeds R l i-1))
    split_ifs
    · exact measurable_const
    exact ((X.enforce_b _ Z).comp hU).mul ((X.charged_b hY hU i l R X.seeds W h).sub measurable_const)
  change Measurable (fun v => X.aura (U v) a i)
  unfold aura; split_ifs
  · exact ((X.cone_b ..).comp hU).sub measurable_const
  exact measurable_const
end masks

section meters
include hY hc
lemma extracts_b (s : Signed) (p : Spot c f) (hp : P.Funds S T) {U : α→Directions G f} (hU : Measurable U) :
    Measurable (fun v => (X.wrapY (Y v)).extracted (U v) s p) := by
  unfold Coat.extracted
  refine Finset.measurable_fun_sum (parents p) ?_; intro i hi
  change Measurable (fun v => if X.selected s (spot S i) then ‖(X.wrapY (Y v)).realPath s i (U v)‖^2/2 else 0)
  split_ifs
  · exact (((X.through hc hp hY hU _ _).norm).pow_const (2:ℕ)).div_const _
  exact measurable_const
lemma principals_b {U : α→Directions G f} (hU : Measurable U) (hp : P.Funds S T) (s : Signed) (p : Spot c f) :
    Measurable (fun v => (X.wrapY (Y v)).debit (U v) s p) ∧ Measurable (fun v => (X.wrapY (Y v)).light (U v) s p) := by
  obtain ⟨hx,ht⟩ := origin_b hp (pull s 0 X.V) (choice s X.k) p X.x
  have hz := pulling_meas s (X.summon hY hU)
  exact ⟨(hx.comp hz).sub (X.extracts_b hY hc _ _ hp hU), (ht.comp hz).sub (X.extracts_b hY hc _ _ hp hU)⟩

lemma vapor_b (h : P.Funds S T) (R : Rep G f) {Ñ : ChartRatio G} (he : LocalRatio Ñ) (a : ℝ) (l : Finset ℕ) (A : Stores S)
    {U : α → Directions G f} (hU : Measurable U) : Measurable (fun v => (X.wrapY (Y v)).steam R Ñ l W a A (U v)) := by
  have ht := X.airwards (v:=fun _=>0) hc h hY
  let v := A.dome (300*X.B)
  let B:= X.plaza (A.dome (304*X.B))
  have hv : Measurable (fun x => (X.wrapY (Y x)).quoteNear A (U x)) := (measurable_const (a:= Raw.orientation)).mul
    (Finset.measurable_fun_sum (M:=ℝ) univ fun s _=> Finset.measurable_fun_sum (posted (turnStore s A) (200*X.B))
      (fun p _ => (X.principals_b hY hc hU h s p).1))
  have hb : Measurable (fun x => (X.wrapY (Y x)).far_bills A) := (measurable_const (a:= Raw.orientation)).mul
    (Finset.measurable_fun_sum (M:=ℝ) univ fun s _ => Finset.measurable_fun_sum (posted (turnStore s A) (200*X.B))
      (fun p _=> X.extracts_b hY hc s p h ht.2.1))
  have hs : Measurable (fun x=> (X.wrapY (Y x)).steamLog R Ñ a A (U x)) :=
    (((((measurable_const (a:=-R.beta)).mul (hv.add hb)).add (measurable_const (a:=∑ i∈visit A (200*X.B),X.condensation i))).add
      (Finset.measurable_fun_sum B (fun i _ => (X.gentry_b i _ he a).comp hU))).sub (measurable_const (a:=(X.pens A).card*Real.log (measure_g Ñ R.beta))))
  let f t := (X.wrapY (Y t)).input (U t); have hf : Measurable f := X.summon hY hU
  have hz : Measurable (fun t=>Mask.profiles A X.χ (300*X.B) X.x W (f t) X.k X.V) := by
    unfold Mask.profiles; dsimp only
    exact (Finset.measurable_fun_prod (readFine v S) (fun i _ => (X.fine_b ..).comp hf)).mul
      (Finset.measurable_fun_prod (readBonds v) (fun i _ => (X.bond_b i A h).comp hf))
  have hw : Measurable (fun t=>Mask.tickets A (300*X.B) (f t) X.k) := (Finset.measurable_fun_prod v
    (fun i _ => (site_b i X.k).comp hf)).mul (Finset.measurable_fun_prod (readBonds v)
      (fun i _ => (pin_b i X.k h).comp hf))
  have hl : Measurable (fun t=>Contract.order R l (vias S A (300*X.B)) (f t)) := Finset.measurable_fun_prod
    _ fun i _ => (contract_b ..).comp hf
  exact ((((Real.measurable_exp.comp hs).mul hl).mul hw).mul hz).mul ((X.enforce_b _ B).comp hU)
end meters
end YM.ConnectedActivityE6.Coat
