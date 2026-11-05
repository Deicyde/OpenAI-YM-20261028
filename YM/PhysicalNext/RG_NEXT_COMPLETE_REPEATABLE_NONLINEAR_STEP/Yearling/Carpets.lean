import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Adorn
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Phial
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Shiner
/-! # A physical transaction: preliminary Compared. Keep explicit parametrization,
    ONE Coat ratio even though gauges arbitrary per step labels. Need the early
 Local rates after cancellations separately.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Yearling
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet March Hues
open Gas Ursell Trees Multiple Alabaster Match Greenbelt Letter
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Geo Ovens RG.Shoot Next.Scheduling
open Push.BetaTransport
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R : ℝ → RG.Rep G f} {U : RG.Rep G f}
    {x μ C v e d D s : ℝ} {i j n m : ℕ} {χ : Chi}

variable {s : Set ℝ} (p : BudgetPoint) (hp : p.threshold=Pressure.temp x) (hf : p.order ≤ j)
   {σ C' Λ : ℝ} (h : T.down.Bounds T.low σ C' Λ) (hd : WilsonStartup.Decent T.low p) (hv : preExponent p/p.B≤ σ/2)
    (H : (i:s)→ Cash W x μ L Q o C T (R i)) (hV:∀ i,Cash.Renewed n e d D (H i))
    (Θ : ∀ i, Year (H i) j v χ) (K : Cash W x μ L Q o C T U) (X:∀ i, Match.Alliance K (H i) 1 0)
    (γ:ℝ) (hX: ∀ i,(X i).units=Equiv.refl _) (A:K.fragrances→RegularAddress c) (hA:∀ z,(A z).support=Song.perf K z)
    (V : ℝ → Collection.Source G c) (hΓ :∀ i : s, V i= plusone K (X i) χ γ)
include H hV Θ X h hp hf hd hv hX hA hΓ
lemma compared (U' : BudgetPoint) (he : ∀ i∈s, (R i).p=U')
    (hr : Curve U' R s) (hd' : ∀ i j:s, (R i).clip=(R j).clip ∧ (R i).path=(R j).path) : Compared (Yearling.booth K p A) p V s:= by
  let P:= Yearling.booth K p A
  apply feathered _ _
  · intro i hi ε hε
    let U : s:= ⟨i,hi⟩
    have hH (i:s):0<(R i).beta := (H i).laws.intake.positive
    have hΦ y (hy:y∈s) : Facing (R i) (R y):= ⟨(he _ hi).trans (he _ hy).symm,(hd' U ⟨_,hy⟩).1,(hd' U ⟨_,hy⟩).2,hr.forced _ hi _ hy, hr.reg _ hi _ hy,hH U,hH ⟨_,hy⟩⟩
    obtain ⟨M,hM,s',hs,hP⟩:= restored (Θ U) p hp hf h hd hv (hV U) γ
    let t:= min s' (ε*M⁻¹); have ht:0<t:= lt_min hs (mul_pos hε (inv_pos.mpr hM))
    filter_upwards [self_mem_nhdsWithin,blue Q.table Q.table_exists hr he hi hΦ t ht] with y hy hq
    let u:s:= ⟨y,hy⟩; rw [show V i=_ from hΓ U, show V y=_ from hΓ u]; obtain ⟨a,b,hF⟩:= hq
    obtain ⟨c,d,hc,hd,hC,hD⟩:= hP (R y) a b t hF (min_le_left ..) ht (H u) (Θ u) (X U) (X u) (hX _) (hX _) _ hA; have hu : t*M≤ ε:= by
      unfold t; calc
        _ ≤ ε*M⁻¹ * M := mul_le_mul_of_nonneg_right (min_le_right ..) hM.le
        _ = _ := by rw [mul_assoc,inv_mul_cancel₀ hM.ne',mul_one]
    exact ⟨c,d,hc,hd,budget_loosen hC hu,budget_loosen hD hu⟩
  intro x hx; rw [show V x=_ from hΓ ⟨x,hx⟩]; exact life (Θ ⟨x,hx⟩) p hp hf h hd hv (hV _) _ γ A hA
end YM.PhysicalNext.Repeat.Yearling
