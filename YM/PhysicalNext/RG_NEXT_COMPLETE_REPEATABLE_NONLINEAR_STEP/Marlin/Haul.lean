import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Alto
/-! # Total merger, given bills. App module Stevens. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Marlin
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} (B : BudgetPoint) (C : Listing G c) (z w : ℕ) {b a q p d Z κ δ : ℝ} {f:ℕ→ℝ}
variable (V : Collection.Source G c) (g t:Trio.Offer G c) (Y: Config G c)
local notation "ℙ" => lodge C z w
local notation "d₀" => bison V g t
local notation "Φ" => raiser B
variable (ht: (C.read V).ForcedFamily B) (he : ∀ s b, Nonempty ((C.read V).Moves s b))
    (hp: Payments.Rates B.B Z a b κ) (hq : ∀ i,0 ≤ f i ∧∀ U, ‖V.hardRead i U‖≤ f i)
    (h : Ac.Hit (fun i=> (C.hard i).support) B.B f (B.supportExponent+1+1) a)
    (hx :∀ i,Trio.Tidy B (neighbors w i) (t i)) (hm : ∀ i U,t i U ≠ 0→ ¬Healthy B.threshold (neighbors w i) U)
    (hv : ∀ i U, ‖t i U‖ ≤ q) (hV : ∀ i : Site c,(coverNumber B.B (neighbors w i):ℝ) ≤ δ) (hG : Marlin.tithe w q B δ ≤ b)
include ht he hp hq h hx hm hv hV hG
lemma stakes : Ingredients (ℙ) (dummy d₀) Φ 0 Z:= by
  have hh:= (norm_nonneg _).trans (hv 0 1); have hb:= Marlin.caps C z w B q hh hV
  have h₀: ((ℙ).pours (d₀)).ForcedFamily B:= ⟨ht.sym,ht.symtest,ht.meas,ht.meas_test,ht.reads,ht.reads_test,ht.permit⟩
  refine Marlin.cannon h₀ (fun s b=> reeds C z w V g t s b (he s b|>.some)) (estateP C z w V g t hx) (failedP C z w V g t hm) (fun s b=> Marlin.gander C z w V g t s b (he s b|>.some)) (fun i U=> ?_) (show Payments.hardCost (raiser B) ℙ f a from ⟨fun i=>(hq i).1,h⟩) ⟨hb.1,fun i=>budget_loosen (hb.2 i) hG⟩ hp
  exact ⟨(hq i).2 U,Marlin.softly V t q hv g i U⟩
end YM.PhysicalNext.Repeat.Marlin
