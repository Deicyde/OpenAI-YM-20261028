import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Survey
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Palette
import YM.Push.FREE_RESOLVENT.Fold


/-!
# Pay grouped Fsct determinant vertices, histogram by hits on complete halo footprint

Project true POSITIVE links to S.parent; assigned neighbourhood includes
both endpoints for dependencies. Support here even when any reach-stencil
comparison fails; may increase l before purchasing. Use these *individual*
values with dictionary of same first-round address. Even where one-turn
word reads MUCH larger limits X, price/hit theorem is on THESE assigned label
supports (can of course purchase for any preassigned increases in our
format). Not getting a hit theorem for arbitrary resized/ancestor support.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.EndpointLoadF16.DetLong
open Function Filter Set Lattice RG Wilson Pressure Tree
open Push.SectorMeasure Next.SectorChange FreeResolvent FreeResolvent.TestD SelectedOrderedKernels
open AnalyticBridge AnalyticBridge.LocalGaussian AnalyticBridge.RelativeLogdet Physical Differential Fund
open Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {V : Config G c} {B : Directions G c}
    {n l k j : ℕ} {x a : ℝ} {T : Tube G S} {A : Stores S} {F : Forest S.ratio} {s : S.Choices} {q : Fund}
    {bp : BudgetPoint} {o : Site c}

def locus (S : StepData c f) (e : Bond f) := S.ratio.parent e.1

def arena (S : StepData c f) (l B : ℕ) : Long f → Support c := Sum.elim (inventory (locus S) l B) (inventory (locus S) l B)




namespace Fund

section numeric
variable (q : Fund)

def combinedCost (G : Gauge) (S : StepData c f) (x : ℝ) (p k : ℕ) (z : Letter (Bond f) j) := Paint.braid (fun w=> q.cost (G:=G) S x p k w) z

def price (G : Gauge) (S : StepData c f) (x : ℝ) (p k : ℕ) : Long f → ℝ :=
    Sum.elim (fun i=> 2*q.combinedCost G S x p k i) (fun i=>2*q.combinedCost G S x p k i)

def overhead (G : Gauge) (S : StepData c f) (x : ℝ) (p k : ℕ) (i : Long f) := Real.exp 1*q.price G S x p k i*myCost k

def introCost (G : Gauge) (n k : ℕ) := 2*∑ _i:G.ColorIndex,q.baseTicket G n k






end numeric

namespace Recital

variable (h : Recital q n k l a x A T F s V B)
include h
lemma weighed : Ac.Hit (arena S l (radiusB x)) (radiusB x) (q.overhead G S x n k) a (currency (q.d/2) (radiusB x)) := by
  let D:= q.letterFee G n k
  let Y:= radiusB x
  let γ:= currency q.d Y
  let E:= 2*D*Real.exp 1*myCost k
  have he : 0≤E := mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (q.amplitude ..).le) (Real.exp_pos _).le) (zero_le_one.trans (myCost_high k))
  let F (j : ℕ) := Paint.braid (fun w:Letter (Key G f) j=> q.micro S x k w)
  have hh (j : ℕ) (i : Letter (Bond f) j) : q.combinedCost G S x n k i=D*F j i := by unfold combinedCost F Paint.braid; rw [Finset.mul_sum]; rfl
  have hp (j : ℕ) (hc : Ac.Hit (inventory (place (G:=G) S) l Y (n:=j)) Y (q.micro S x k) a γ) :
      Ac.Hit (inventory (locus S) l Y) Y (fun i=> E*F j i) a (E*γ) := by
    have ht:= Paint.genuine (fun w:Letter (Key G f) j=> q.micro S x k w) (locus S) Y l a γ hc
    intro o
    exact SumBudget_squeeze _ (ht o) he
  let f₁ := fun i=> E*F 1 i; let f₂:= fun i=> E*F 0 i
  have hF : q.overhead G S x n k=Sum.elim f₁ f₂ := by
    funext i; cases i
    · change Real.exp 1*(2*q.combinedCost G S x n k _)*myCost k= E*_; rw [hh]; unfold E; ring
    change Real.exp 1*(2*q.combinedCost G S x n k _)*myCost k= E*_; rw [hh]; unfold E; ring
  rw [hF]; have hz := Labels.together _ _ Y (hp 1 h.paid.size') (hp 0 h.paid.size)
  have hx : E*γ+E*γ=q.finalCost G n k*γ := by unfold E D finalCost; ring
  intro o; exact budget_loosen (hz o) (hx.trans_le h.combined)
-- helper for hit scaling
where
  SumBudget_squeeze {ι : Type} (E : ℝ) {g : ι → ℝ} {P : ι → Prop} [DecidablePred P] {a : ι → ℝ} {γ : ℝ}
    (h : SumBudget (fun i=> if P i then g i*a i else 0) γ) (he : 0≤E) :
    SumBudget (fun i=> if P i then E*g i*a i else 0) (E*γ) := by
    simpa only [mul_assoc, mul_ite, mul_zero] using budget_scale he h



section publish
variable (hp : bp.power=n) (o : Site c)
include hp




lemma bound_diag (i : Bond f) : Ticket (bp.dirBound o) k (increment V B)
    (∑ _j:G.ColorIndex,q.baseTicket G n k) (arc (locus S i) o n) (chapters x T A F s (.inl i)) := by
  change Ticket _ _ _ _ _ (∑ j, simple x T A F s (i,j))
  exact Ticket.sum (arc_pos ..).le (f:=fun j=>simple x T A F s (i,j)) (w:=fun _=>q.baseTicket G n k) (r:=arc (locus S i) o n) (U:=_) (fun j _=>h.simple_ticket hp (i,j) o)

omit h hp in
lemma scale_one {u : Config G c→ ℝ} {k : ℕ} {D : Directions G c→Prop} {B C r : ℝ} (h : Ticket D k V C r u)
    (hB : ‖B‖≤1) : Ticket D k V C r (fun v=> B*u v) := by
  apply Ticket.mono (h.indiv B) _ le_rfl
  exact mul_le_of_le_one_left h.price_nonneg hB

variable (h0 : Recital q n k l a x (voidStore S) T F s 1 0)
include h0
lemma bound_prelude (i : Bond f) : Ticket (bp.dirBound o) k (increment V B) (q.introCost G n k) (arc (locus S i) o n)
    (prelude x T A F s i) := by
  have ht := (h0.bound_diag hp o i).base; rw [Work.G07.at_zero_increment] at ht
  let F₁:_:= chapters x T (voidStore S) F s (.inl i) 1
  have hh:= h.bound_diag hp o i
  have he:= hh.sub ((Ticket.pure hh.radius_nonneg F₁).mono ht le_rfl)
  unfold introCost; rw [two_mul]
  exact scale_one he (by norm_num)




end publish
end Recital
end Fund
end YM.PhysicalNext.EndpointLoadF16.DetLong
