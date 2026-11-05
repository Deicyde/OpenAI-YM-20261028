import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Income
/-! # ∑ over Actual potentials. Shoot.deviation & passport exchange through crown.
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
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I U : RG.Rep G f}
    {x μ C v e d D t t' : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W x μ L Q o C T R}

lemma bounty (c : Side) (p : BudgetPoint) : ∃ K: ℝ,1 ≤ K∧∀ (ι:Type) (X:ι→Support c) (v:ι→ℝ) (M:ℝ), SumBudget v M→ SumBudget (fun i=> p.mass (X i) (v i)) (K*M):= by
  let K := Real.exp (p.supportExponent * (Fintype.card (Site c):ℝ)); have hK:1 ≤ K:= Real.one_le_exp (mul_nonneg p.exponent_pos.le (Nat.cast_nonneg _))
  refine ⟨K,hK,?_⟩; intro i X v M H; refine budget_mono (budget_scale (zero_le_one.trans hK) H) (fun i=>mul_nonneg (Real.exp_nonneg _) (H.1 _)) (fun i=>?_)
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show (coverNumber p.B (X i):ℝ) ≤ (Fintype.card (Site c):ℝ) from by
    exact_mod_cast ((coverNumber_realized p.B (X i)).choose_spec.2.symm.le.trans ((coverNumber_realized p.B (X i)).choose.card_le_univ))) p.exponent_pos.le)) (H.1 _)
lemma voyages (p : BudgetPoint) {E : Type} (U : E→RegularAddress c) (d z : E→ Config G c→ℝ) (w:E→ℝ) (h : ∀ i, p.Regular (U i).support (d i) ∧ p.Regular (U i).support (z i) ∧ p.supBounds (U i).site (U i).support (d i-z i) (t*w i)) :
   let v (i:Seat c × E):= Rim c*(turnFee p*w i.2)
   ∀ i, Shoot.variesRegular p (revolve U i) (choir d i) (choir z i) (t*v i):= by
  intro v i
  obtain ⟨θ,i⟩:=i; obtain ⟨hp,hv,hd⟩:= h i; let C:=Rim c
  apply (sup_varies (d:=revolve U (θ,i)) (p:=p) (f:=choir d (θ,i)) (g:=choir z (θ,i)) (CouplingShape.reg_scale _ (Seat.regular _ hp)) (CouplingShape.reg_scale _ (Seat.regular _ hv))).2
  have hx: choir d (θ,i)-choir z (θ,i)=choir (d-z) (θ,i):= by unfold choir; ext; simp; ring
  have hh:= CouplingShape.sup_scale C (Song.transSup θ (CouplingShape.reg_sub hp hv) hd)
  rw [hx]; apply sup_le hh; apply le_of_eq; rw [abs_of_nonneg (rim_nn c)]; change C*_ =t*(C*(turnFee p*w i)); ring

-- full/.door gauge. Exact lattice.W
variable (Θ : Year H j v χ) (p : BudgetPoint) (hp : p.threshold=Pressure.temp x) (hf : p.order ≤ j)
   {σ C' Λ : ℝ} (h : T.down.Bounds T.low σ C' Λ) (hd : WilsonStartup.Decent T.low p) (hv : preExponent p/p.B≤ σ/2) (hΨ : Cash.Renewed n e d D H)
include Θ hp hf h hd hv hΨ
lemma restored (γ:ℝ) : ∃ K:ℝ,0 < K∧ ∃ s:ℝ,0<s∧∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ),Equalized Q.table R I a b t→ t ≤ s →0<t →∀ (H':Cash W x μ L Q o C T I),Year H' j v χ→∀ {V:RG.Rep G f} {H₀:Cash W x μ L Q o C T V} (X:Match.Alliance H₀ H 1 0) (Y:Match.Alliance H₀ H' 1 0), X.units=Equiv.refl _→ Y.units=Equiv.refl _→∀ P:H₀.fragrances→RegularAddress c,(∀ z,(P z).support=Song.perf H₀ z) →
      let u : Listing G c:={posting p H₀ with reg:=revolve (Sum.elim P (strings T.down p)) ∘ Song.pennant H₀}
      deviation p (u.read (plusone H₀ X χ γ)) (u.read (plusone H₀ Y χ γ)) (t*K):= by
  obtain ⟨M,hM,s,hs,hP⟩:= ritual p Θ hp hf h hd hv γ -- order
  obtain ⟨Q',hQ,q,hq,hX⟩:= favor Θ hΨ
  obtain ⟨A,hA,h'⟩:= bounty c p
  let C:= Rim c; let k:= Fintype.card (Seat c); let z := k * (C*(turnFee p*M)); let v:= 1+(A*z+A*Q')
  have hp:= turnFee_pos p; have hc:0≤C:= rim_nn _; have hh:0 ≤ z:=by unfold z; positivity
  have hg:= mul_nonneg (zero_le_one.trans hA) hh; have hQ':= mul_nonneg (zero_le_one.trans hA) hQ
  refine ⟨v, show 0<v from (by unfold v; positivity),min s q,lt_min hs hq,?_⟩; intro I a b t he hu ht H' Θ' V H₀ X Y hx hy P hO u
  obtain ⟨w,hw,hU⟩:= hP I a b t he (hu.trans (min_le_left ..)) ht H' Θ' X Y hx hy P hO
  obtain ⟨f,hF,he⟩:= hX I a b t he (hu.trans (min_le_right ..)) ht H' Θ' X Y hx hy
  let F(i:Seat c × Magazine H₀):= Rim c*(turnFee p*w i.2)
  let Z:ℕ→ℝ:=F ∘ Song.pennant H₀; have hz : SumBudget Z z:= Cost.equiv (Song.pennant H₀) (Cost.product (f:=fun _=> C*(turnFee p*M)) (Cost.finite _ (by positivity)) (fun _=> (budget_scale hc (budget_scale hp.le hw))))
  let D:=f ∘ Refrain.badge H₀; have hT: SumBudget D Q':= Cost.equiv _ hF
  refine ⟨fun i=>t* Z i, fun i=>t*D i, fun i=> ?_,fun i=> ⟨mul_nonneg ht.le (hT.1 i),fun U=> he _ U⟩,budget_loosen (h' ℕ _ _ _ (budget_scale ht.le hz)) ?_, budget_loosen (h' ℕ _ _ _ (budget_scale ht.le hT)) ?_⟩
  · exact voyages p _ (opus H₀ X χ γ) (opus H₀ Y χ γ) w hU (Song.pennant H₀ i)
  · unfold v; nlinarith only [ht, mul_nonneg ht.le hQ']
  unfold v; nlinarith only [ht,mul_nonneg ht.le hg]
end YM.PhysicalNext.Repeat.Yearling
