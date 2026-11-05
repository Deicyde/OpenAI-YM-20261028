import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Bison
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shingle.Mild
/-!
 # Actual front/retirement pruning along a bend. Local hard prices after Renato.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Shingle
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio Marlin Slide Push.BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L C:Side} {B : BudgetPoint} {X Z: Support c} {z w : ℕ} {e p d a δ Y : ℝ} {x:ℝ} {s:Set ℝ} {ι:Type}
lemma shaping {f:ℝ→ Config G C→ℝ} (hp:Mild B univ f s) (A:Track C) (o:Site c) (he : ∀ i:Site C, separation o (Slide.sites A o i)≤w):
    Mild B (neighbors w o) (fun x=> f x ∘ shape A o) s:= by
  have hh i (hi:i∈s): B.Regular (neighbors w o) (f i ∘ shape A o):= Slide.regular A o (hp.smooth i hi) fun i=> (neighbors_mem ..).2 (he i)
  refine Mild.tagged hh (Marlin.leap w o) rfl ?_; intro x hx ε hε
  let M:=2^B.order*(1+(w:ℝ))^(B.power*B.order); have hm:0<M:= by unfold M; positivity
  filter_upwards [self_mem_nhdsWithin,hp.budget x hx 0 (ε/M) (by positivity)] with i hi hP
  apply (sup_varies (hh x hx) (hh i hi)).2; refine ⟨hε.le,fun V hv l hl hd=>?_⟩
  have hV : flags B.threshold (shape A o V)=∅:= Slide.allFlag A o V (neighbors w o) (fun i=> (neighbors_mem ..).2 (he i)) _ B.threshold_pos.le hv
  have hG: Healthy B.threshold univ (shape A o V):= by unfold Healthy; rw [hV]; simp
  let f' := f x-f i
  have hu:= Slide.stalled A o f' he l V hl hd ((VerifiedReset.reg_sub (hp.smooth x hx) (hp.smooth i hi)).smooth _ hG) (fun j hj ht=> hP.2 _ hG j hj fun i hi=>Boulevard.tiny (ht i hi) _)
  exact hu.trans_eq (show M*(ε/M)=ε from (by field_simp))
lemma litIn {c:Side} (Z: Listing G c) {h:ℝ→ Collection.Source G c} (i:ℕ) (hp:Compared Z B h s) (hv :∀ x∈s,B.Regular (Z.reg i).support ((h x).logRead i)) : Mild B (Z.reg i).support (fun x=> (h x).logRead i) s:= Mild.tagged hv _ rfl fun x hx d he=> hp.values x hx|>.1 i d he
namespace Mild
variable {S : StepData c L} {T:Tube G S} {K₀:Teller G} {X : ConnectedActivityE6.Target G K₀} {θ: Target.Order G p} {L₀ : Side}
variable (k:ℕ) {R: RG.Rep G L} (A: Cash p e d L₀ X θ a T R)
    {D:ℝ→ Offer G c} {V : ℝ→ Collection.Source G c} (he : Compared (Beam.marquee A B) B V s)
    (ht : B.B=radiusB e)
local notation "P₀" => (Beam.marquee A B)
variable (hv:∀ x∈s,∀ i,B.Regular ((Beam.marquee A B).reg i).support ((V x).logRead i))
def omen (B:BudgetPoint) (A:Cash p e d L₀ X θ a T R) (k:ℕ) (V:Collection.Source G c) (i:Site c): Config G c→ℝ:= ∑ x∈ Meadow.panel A k, Meadow.garnerAt A B i x •(V.logRead x)
include he ht hv
lemma attic (i:Site c) (hz : ∀ x∈s,D x i= omen B A k (V x) i): Mild B (neighbors (Meadow.studio X.halo B.B) i) (fun x=>D x i) s:= by
  have hz:∀ x∈s, D x i=∑ x'∈Meadow.panel A k, Meadow.garnerAt A B i x' • ((V x).logRead x'):= hz
  let C (x:ℝ) :=∑ x'∈Meadow.panel A k, Meadow.garnerAt A B i x' • ((V x).logRead x')
  let t:=neighbors (Meadow.studio X.halo (radiusB e)) i
  have ht₀:Mild B t C s:= by
    refine Mild.total (g:=fun x' x=> Meadow.garnerAt A B i x' • (V x).logRead x') (Meadow.panel A k) fun p hp=> ?_
    have h:= litIn P₀ p he (fun x hx=>hv x hx p)
    have hl := h.scale (Meadow.garnerAt A B i p)
    by_cases h: Meadow.garnerAt A B i p=0
    · simp only [h,zero_smul]; refine ⟨fun x hx=> CouplingShape.reg_const _,fun x hx i ε he=> ?_⟩; filter_upwards with y; rw [sub_zero]; exact VerifiedReset.sup_le (CouplingShape.sup_const 0) (by rw [abs_zero]; exact he.le)
    exact hl.mono (Meadow.assigned A B i p hp ht h).2
  have hh:Mild B (neighbors (Meadow.studio X.halo (radiusB e)) i) (fun x=> D x i) s:= ht₀.aboard id continuous_id.continuousOn (fun _=>id) hz
  rw [show neighbors (Meadow.studio X.halo B.B) i=t from congr_arg (fun y:ℕ=> neighbors (Meadow.studio X.halo y) i) ht]; exact hh
end Mild

end YM.PhysicalNext.Repeat.Shingle
