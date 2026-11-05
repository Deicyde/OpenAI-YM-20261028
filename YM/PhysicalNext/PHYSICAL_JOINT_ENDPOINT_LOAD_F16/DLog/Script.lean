import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Counter
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Fund

/-!
# Earn the individual letter tickets with log-domain order, scroll envelope too

Everything still with tag/panel tests held, using Stipend's actual ordered
powers in the chart. These are substrate prices. Fsct signs & retained-tag
comparator costs (no changing stencils nor symmetry tests on averaged colors)
in the next parts. Pay even the integrals of ABSOLUTE differentiated envelopes;
no using cancellation in u or between adjacent lengths or across different
frozen arguments. Keep the E-smoothing gap for paying every length with its
full halo. No license here for graph/tag comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.EndpointLoadF16.DetLong
open Function Filter Set MeasureTheory Lattice RG Wilson Pressure Tree Matrix
open Next.SectorChange Next.Fluctuations.Sector
open FreeResolvent FreeResolvent.TestD FreeResolvent.Affine SelectedOrderedKernels
open AnalyticBridge AnalyticBridge.LocalGaussian AnalyticBridge.RelativeLogdet Physical Differential
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {V : Config G c} {B : Directions G c}
    {n l k : ℕ} {x a : ℝ} {T : Tube G S} {A : Stores S} {F : Forest S.ratio} {s : S.Choices} {q : Fund}
    {bp : BudgetPoint} {o : Site c}
section grammar
variable (x T A F s)

/-- Color terms for A and A flat (flat is the empty allocation at 1). -/
def simple (i : Key G f) (v : Config G c) : ℝ := letterBase (windows S x) (AFull T A F x v s) i

def correction (w : Letter (Key G f) 1) (v : Config G c) : ℝ := page (windows S x) (AFull T A F x v s) w



def intervalCharge (w : Letter (Key G f) 0) (v : Config G c) : ℝ := errata (windows S x) (AFull T A F x v s) w
end grammar

open Fund
namespace Fund.Recital
variable (h : Recital q n k l a x A T F s V B)
include h

/-- Insist on the complete additive-basis test, prior to off-center
order. Even when o arbitrary the anchor of the Mark at this stage is
specified by the address. -/
lemma small_bill (i : Key G f) (L : List (raw G c)) (hL : L.length ≤ k) :
    let g := simple x T A F s i
    ContDiffAt ℝ k (SelectedOrderedKernels.over g V) ((paint G c).symm B) ∧
      (marked G c (q.growth k)).pay L (place S i) * |strike V B g L| ≤ (q.D+1)*q.D := by
  obtain ⟨he,-,-,hi⟩ := h.maestro.1.standard L i hL
  refine ⟨he,hi.trans ?_⟩
  split
  · rfl
  have H:=q.coin; nlinarith only [H]









variable (hp : bp.power=n)
include hp

lemma simple_ticket (i : Key G f) (o : Site c) :
    Ticket (bp.dirBound o) k (increment V B) (q.baseTicket G n k) (arc (place S i) o n) (simple x T A F s i) := by
  have he := h.small_bill i
  have hy : 0≤ q.D := zero_le_one.trans q.coin
  exact publish h.reach (q.growing k).1 hp (mul_nonneg (add_nonneg hy zero_le_one) hy)
    (he [] (by simp)).1 (fun L hL => (he L hL).2)








end Fund.Recital
end YM.PhysicalNext.EndpointLoadF16.DetLong
