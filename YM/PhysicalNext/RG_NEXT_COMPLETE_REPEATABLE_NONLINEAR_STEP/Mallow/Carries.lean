import YM.Further.DENSE_MIXED_KERNELS.AtWork
import YM.Further.DENSE_MIXED_KERNELS.Stroke
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Foam

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
variable {G : Gauge} {c L:Side} (B : BudgetPoint) (C : Listing G c) (z w : ℕ) {p d a δ q Y E : ℝ}
variable (T : Collection.Source G c) (g t:Trio.Offer G c) (V:Config G c)
local notation "P" => lodge C z w
local notation "U" => (bison T g t)
local notation "θ" => (C.read T)
local notation "N" => pluck B (lodge C z w)
local notation "D" => poursP B (lodge C z w) U
-- apply for χ(T!). scalar V0
variable {R : Listing G c} (F : Collection.Source G c) (hf : ∀ i,R.hard i=C.hard i ∧ F.hardRead i=T.hardRead i) (W : PathData G) (b : Clip) (β τ φ x : ℝ)
   (hV : Ingredients (lodge C z w) (dummy (bison T g t)) (raiser B) 0 Y)
lemma cruiseV (h : Meadow.Budget B C.reg T.logRead E) (ht: ∀ V:Config G c,(R.read F).additive B V= (θ).additive B V+Fintype.card (Site c)*x + (∑ i, masked B.threshold (neighbors z i) (g i) V)+∑ i:Site c,t i V)
    (hs:∀ s b, Nonempty ((R.read F).Moves s b)) (hp:∀ s b,Nonempty ((C.read T).Moves s b)) :
    (Collection.frozen R W b B F β τ).exponent V=(Collection.frozen (N) W b B (D) β (τ-x)).exponent V+(∑' i,(U).logarithm i V):= by
  let X := (P); let y:=leanU c; let f i:= masked B.threshold (sea z i).support (choir (g) i) V; let t' (i: Door c):=choir (-t) i V
  have he : (((N).read D).additive B V)=(θ).additive B V +∑ i,f i:= by
    let g'(i: Civ c):= Sum.elim (fun i=>(θ).regularOccurrence B i V) f i
    have hh : ∀ i:Civ c, ((N).read D).regularOccurrence B (y.symm i) V=g' i:= by intro i; change masked _ (Sum.elim C.reg (sea z) (y (y.symm i))|>.support) (Sum.elim _ _ (y _)) _= _; rw [Equiv.apply_symm_apply]; cases i<;> rfl
    have hu : (N|>.read D).additive B V=∑' i,g' i := by
      rw [← y.tsum_eq g']; unfold Activities.additive; refine tsum_congr fun i=>?_ ; rw [← hh,Equiv.symm_apply_apply]
    rw [hu]; exact Summable.tsum_sum (f:=g') (stashes B C T V h) Summable.of_finite|>.trans (congr_arg ((θ).additive B V + ·) (tsum_fintype f))
  have hg : ∑' i,(U).logarithm i V= ∑ i,t' i:= by
    let f' : Civ c→ℝ:= Sum.elim 0 t'
    have hp : ∑' i,(U).logarithm i V=∑' i, f' (y i):= by refine tsum_congr (fun i=>?_); change Sum.elim (fun _:ℕ=> (0:Config G c→ℝ)) (choir (-t)) (y i) V=_; cases y i <;> rfl
    rw [hp,y.tsum_eq f', Summable.tsum_sum (f:=f') (show Summable (fun i : ℕ=> f' (.inl i)) from summable_zero) Summable.of_finite]; simp [f']
  let c':=(Fintype.card (Site c):ℝ)
  have hA:(R.read F).additive B V - (θ).additive B V- c'*x=(∑ i,f i)- ∑ i,t' i:= by
    let gb (u:Seat c):= (R.read F).additive B V - (θ).additive B V-c'*x
    have h(u: Seat c): (∑ i:Site c,f (u,i)) - ∑ i:Site c,t' (u,i)=Rim c*gb u := by
      have hb: (R.read F).additive B (u.view V)= (R.read F).additive B V:= streams B V F 0 u.1 u.2 _ (hs _ _|>.some)
      have hp: (θ).additive B (u.view V)= (θ).additive B V:= streams B V T 0 u.1 u.2 _ (hp _ _|>.some)
      have ht:= ht (u.view V); rw [hb,hp] at ht
      have hv i:t' (u,i)=Rim c * (-(t i (u.view V))):=rfl
      have hF i:f (u,i)=_:= tune (leap z) g u i V B -- Offer binder issue
      simp_rw [hF,hv, ← mul_sum,Finset.sum_neg_distrib]; unfold gb; rw [ht]; change _-_ = _ * (_+c'*x+_+_-_- _); ring -- edit
    rw [Fintype.sum_prod_type (f:=f), Fintype.sum_prod_type (f:=t'),← sum_sub_distrib]; simp_rw [h]; unfold gb; rw [sum_const,card_univ,nsmul_eq_mul, ← mul_assoc,Song.balance,one_mul]
  unfold RG.Rep.exponent; dsimp only [Collection.frozen]; rw [hg,he]; linarith

end YM.PhysicalNext.Repeat.Marlin
