import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Fluent
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Nips
/-!
 # ∆ Books at fixed lattice. Warp did not translate masks or charge views
    over rotations again without accounting. Can anchor E at **any** x (moment
    polynomial constant paid entire lattice).
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
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Geo Ovens
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I U : RG.Rep G f}
    {x μ C v e d D : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W x μ L Q o C T R}
lemma chargedAt (p : BudgetPoint) {ι : Type} (W:ι→ℝ) (X : ι→RegularAddress c) (hp : ∀ i,0≤ W i) (h : Quotes.early p X W e): Summable W:= by
  let f o i:= if (X i).site=o then W i*Real.exp (preExponent p*coverNumber p.B (X i).support) else 0
  have hf (o:Site c):SumBudget (f o) e:=h o; have hz:= budget_over univ f _ fun x _=> hf x
  refine hz.2.1.of_nonneg_of_le hp (fun i=> le_trans (b:=f (X i).site i) ?_ (single_le_sum (f:=fun o=>f o i) (fun x _=> (hf x).1 i) (mem_univ _)))
  unfold f; rw [if_pos rfl]; have he: 0 ≤ preExponent p:= by unfold preExponent; have hP:= p.exponent_pos; linarith
  exact le_mul_of_one_le_right (hp _) (Real.one_le_exp (by positivity))
variable (p : BudgetPoint)
lemma aster (P : PathData G) (l : Clip) (γ : ℝ) {σ C Λ : ℝ} (h : P.Bounds l σ C Λ) (hd : WilsonStartup.Decent l p) (hv : preExponent p/p.B≤ σ/2) : ∃ f:Songbook c→ℝ, Summable f ∧ ∀ β β' j,
    let Z:= strings P p (n:=c) j
    let Y β:= sounding P l β γ j
    p.Regular Z.support (Y β) ∧ p.supBounds Z.site Z.support (Y β-Y β') (|β-β'| * f j) ∧ 0≤f j:= by
  obtain ⟨u,hU,ht⟩:=stanzaReady (n:=c) P l p 1 γ h hd hv
  obtain ⟨v',hV,hT⟩:= stanzaReady (n:=c) P l p 0 γ h hd hv
  refine ⟨u+v',(chargedAt p _ _ (fun i=> (ht i).2.1) hU).add (chargedAt p _ _ (fun i=> (hT i).2.1) hV),?_⟩; intro s t i Z Y
  obtain ⟨k,hk,hx⟩:=stanzaReady (n:=c) P l p s γ h hd hv
  refine ⟨(hx i).1,?_, add_nonneg (ht i|>.2.1) (hT i|>.2.1)⟩
  have he':Y s-Y t=fun v=> (s-t)*(Y 1 v-Y 0 v):= by ext; unfold Y sounding; rcases i with i|i|i|i<;>dsimp only [tuneAtom,tuneLow,Pi.sub_apply,Pi.smul_apply, smul_eq_mul, Sum.elim]<;> ring
  rw [he']; exact CouplingShape.sup_scale _ (CouplingShape.sup_sub (ht i|>.1) (hT i|>.1) (ht i|>.2) (hT i|>.2))

variable (Θ : Year H j v χ) (hp : p.threshold=Pressure.temp x) (hf : p.order ≤ j)
   {σ C' Λ : ℝ} (h : T.down.Bounds T.low σ C' Λ) (hd : WilsonStartup.Decent T.low p) (hv : preExponent p/p.B≤ σ/2)
include Θ hp hf h hd hv
theorem ritual (γ:ℝ) : ∃ K:ℝ,0 ≤ K ∧∃ s:ℝ,0 < s∧∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ),Equalized Q.table R I a b t→ t ≤ s →0<t →∀ (H':Cash W x μ L Q o C T I),Year H' j v χ→ ∀ {V:RG.Rep G f} {H₀ : Cash W x μ L Q o C T V} (X:Match.Alliance H₀ H 1 0) (Y: Match.Alliance H₀ H' 1 0), X.units=Equiv.refl _→ Y.units=Equiv.refl _→ ∀ P:H₀.fragrances→RegularAddress c,(∀ z,(P z).support= Song.perf H₀ z) →
    ∃ f:Magazine H₀→ℝ, SumBudget f K ∧∀ i: Magazine H₀, let z:= Sum.elim P (strings T.down p) i; let a:= opus H₀ X χ γ i; let b:= opus H₀ Y χ γ i
       p.Regular z.support a ∧ p.Regular z.support b ∧ p.supBounds z.site z.support (a-b) (t*f i):= by
  obtain ⟨M,hM,s,hs,hx⟩:= fext Θ p hp hf
  obtain ⟨f',hE,H'⟩:= aster (c:=c) p T.down T.low γ h hd hv; have he i: 0 ≤ f' i:= (H' 0 0 i).2.2
  let k:= ∑' i,f' i; have hh : SumBudget f' k:=⟨he,hE,le_rfl⟩
  refine ⟨M+k,add_nonneg hM (Cost.nonneg hh),s,hs,?_⟩; intro I a b t hY ht hv H₁ Hx V H₀ X Y H K A hA
  obtain ⟨g,hg,hP⟩:= hx I a b t hY ht hv H₁ Hx X Y H K
  let F:Magazine H₀→ℝ:= Sum.elim g f'; refine ⟨F,Cost.sum (f:=F) hg hh,?_⟩; intro i z x y
  rcases i with i|i
  · dsimp only [z,Sum.elim]; rw [hA]
    exact ⟨(Song.pocketScore p H₀ X χ Θ.net hp hf p.power le_rfl i).1,(Song.pocketScore p H₀ Y χ Hx.net hp hf p.power le_rfl i).1,hP i _⟩
  obtain ⟨ha,hv',-⟩:= H' R.beta I.beta i; exact ⟨ha,(H' I.beta 0 i).1,sup_le hv' (mul_le_mul_of_nonneg_right hY.β (he i))⟩
omit hp hf h hd hv in
lemma favor (h : Cash.Renewed n e d D H) : ∃ M:ℝ,0≤ M ∧∃ s:ℝ,0 < s∧∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ),Equalized Q.table R I a b t→ t ≤ s →0<t →∀ (H':Cash W x μ L Q o C T I),Year H' j v χ→ ∀ {V:RG.Rep G f} {H₀ : Cash W x μ L Q o C T V} (X:Match.Alliance H₀ H 1 0) (Y: Match.Alliance H₀ H' 1 0), X.units=Equiv.refl _→ Y.units=Equiv.refl _→
     ∃ f:Refrain.Annual H₀→ℝ, SumBudget f M ∧∀ i U, |Refrain.fuse H₀ X χ i U - Refrain.fuse H₀ Y χ i U| ≤ t*f i:= by
  obtain ⟨M,hM,s,hs,hY⟩:= faces Θ h
  refine ⟨M,hM,s,hs,?_⟩; intro I a b t hp ht hv H' hV V H₀ X Y hX hh; let Z: Alliance H H' 1 0:= staple hp.path hp.reg hp.forced
  obtain ⟨f,hF,hK⟩:= hY I a b t hp ht hv H' hV Z rfl
  let y:Refrain.Annual H₀→ℝ:= Sum.elim (fun i=> f (X.tongs i.val)) (fun _=>0)
  refine ⟨y,budget_loosen (Cost.sum (f:=y) (budget_pull (X.tongs ∘ Subtype.val) (X.tongs.injective.comp Subtype.val_injective) hF) (show SumBudget (fun i=> y (.inr i)) 0 from (by simp [SumBudget,y]))) (by rw [add_zero]),?_⟩; intro p U; rcases p with p|p
  · unfold Refrain.fuse; dsimp only [Sum.elim]; rw [abs_sub_comm,←patrol X Z Y hX rfl hh]; exact hK _ _
  simp [y,Refrain.fuse]
end YM.PhysicalNext.Repeat.Yearling
