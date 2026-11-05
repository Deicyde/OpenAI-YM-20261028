import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Bison
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Pylon
/-!
 # Assessment; K capacitance by TURN orbit. no slack in Book threshold.
 Finish on Bison data: same across Beta. -/
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
variable {G : Gauge} {c L:Side} {P : BudgetPoint} (C : Listing G c) (z w : ℕ) {p d a δ : ℝ}
variable (B:BudgetPoint) (U : Collection.Source G c) (g : Trio.Offer G c)
-- K arm genealogy prices posted before gauges. α includes turn width.

def tract (c:Side) (b:ℝ) (i:Civ c):ℝ:= Sum.elim (fun _=>0) (fun _=> Rim c*b) i
def tithe (w : ℕ) (b : ℝ) (P:BudgetPoint) (e:ℝ):= (ballCost w:ℝ)*b* Real.exp ((P.supportExponent+1+1)*e)
lemma caps (b:ℝ) (h:0 ≤ b) (hT: ∀ i:Site c,(coverNumber B.B (neighbors w i):ℝ) ≤ δ): Payments.softCost (raiser B) (Marlin.lodge C z w) (tract c b ∘ leanU c) (tithe w b B δ):= by
  let U:= lodge C z w; let H : Civ c→Support c:=RegularAddress.support ∘ Sum.elim C.reg (sea w)
  have he i : 0≤tract c b i:=by
    rcases i with i|i; · rfl
    exact mul_nonneg (rim_nn _) h
  refine ⟨fun i=> he _, fun x=> budget_pull (w:=fun i=> if x∈ H i then tract c b i * Real.exp ((B.supportExponent+1+1)*coverNumber B.B (H i)) else 0) (leanU c) (leanU c).injective ?_⟩
  set f : Civ c→ℝ:= (fun i=> if x∈ H i then _ else _) with hf
  have h i : 0≤f i:= by unfold f; split; exact mul_nonneg (he _) (Real.exp_nonneg _); exact le_rfl
  let F := Real.exp ((B.supportExponent+1+1)*δ); let e:= Rim c; have hg:0≤e:=rim_nn _; have hb:=B.exponent_pos
  have hh : SumBudget (fun i: Door c=> f (.inr i)) (tithe w b B δ):= by
    apply budget_finite (fun i=> h (.inr i)); rw [Fintype.sum_prod_type]
    let v:=e*b*F
    have hx θ : ∑ i:Site c,f (.inr (θ,i))≤(ballCost w:ℝ)*v:= by
      let p:= Push.Local.turnSites θ.1 θ.2; let s:= neighbors w (p.symm x)
      have hB i: coverNumber B.B (H (.inr (θ,i))) = coverNumber B.B (neighbors w i):= Push.Local.cover_map p (Push.Local.turn_sep _ _) B.B (neighbors w i)
      have hp i (hi:x∈ H (.inr (θ,i))): i ∈ s:= by
        obtain ⟨j,hj,hx⟩:= Finset.mem_image.mp hi; rw [show s=neighbors w j from congr_arg (neighbors w) ((Equiv.symm_apply_eq p).mpr (show x=p j from hx.symm))]; rw [neighbors_mem, separation_comm]; exact (neighbors_mem ..).mp hj
      have hq i: f (.inr (θ,i)) ≤ if i∈s then v else 0:= by
        unfold f; split
        next hv =>rw [if_pos (hp _ hv),hB]; apply mul_le_mul_of_nonneg_left ?_ (he (Sum.inr (θ,i))); apply Real.exp_le_exp.mpr _; exact mul_le_mul_of_nonneg_left (hT i) (by linarith)
        split; unfold v F; positivity; rfl
      refine (sum_le_sum (fun i _=> hq i)).trans ?_; rw [← Finset.sum_filter,filter_mem_eq_inter, Finset.univ_inter,sum_const, nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) (by unfold v F; positivity)
    refine le_trans (sum_le_sum (fun i _=> hx i)) (le_of_eq ?_); rw [sum_const,card_univ,nsmul_eq_mul]; unfold tithe v e F; field_simp [Rim]
  rw [← zero_add (tithe ..)]; exact Cost.sum (f:=f) (show SumBudget (fun i=> f (.inl i)) 0 from by unfold f; simp [tract,SumBudget]) hh

lemma softly (a:ℝ) (hp : ∀ i V, ‖g i V‖ ≤ a) (v:Trio.Offer G c) (i:ℕ) (V) : ‖(bison U v g|>.logarithm i V)‖ ≤ Marlin.tract c a (leanU c i):= by
  let d:= Sum.elim (fun _:ℕ=>0) (Song.choir (-g)); change ‖d (leanU c i) V‖ ≤ _
  cases leanU c i
  · change ‖(0:ℝ)‖ ≤ 0; rw [norm_zero]
  next j=> change ‖Rim c * (-(g j.2 (j.1.view V)))‖ ≤ _; rw [norm_mul,norm_neg,Real.norm_of_nonneg (rim_nn _)]; exact mul_le_mul_of_nonneg_left (hp _ _) (rim_nn _)
end YM.PhysicalNext.Repeat.Marlin
