import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shingle.Chutes
/-! # AtEach convergence hard sparks after all census. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Shingle
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio Marlin Push.BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {B : BudgetPoint} {X : Listing G c} (z w : ℕ) {e p d a δ Y : ℝ} {x:ℝ} {s:Set ℝ}
-- uniform rescale costs
variable {ι A:Type*} {f: ι→ ℝ→A→ℝ}
lemma productsA [Nonempty A] (F:Finset ι) (v:ι→ℝ) (h : ∀ i∈F,Varies (f i) x s) (he:∀ i∈F,∀ U, ‖f i x U‖≤ v i) : Varies (fun x U=>∏ i∈F,f i x U) x s:= by
  have h' i (hi:i∈F):0≤ v i:= (norm_nonneg _).trans (he i hi (Classical.arbitrary A))
  induction F using Finset.induction_on with
  | empty=> simp_rw [Finset.prod_empty]; exact Varies.fixed _
  | @insert i F hi ih=>
    have heK (i) (hv:i∈F) := he i (mem_insert_of_mem hv)
    simp_rw [prod_insert hi]; apply Varies.product (h i (mem_insert_self ..)) (ih (fun i hi=> h i (mem_insert_of_mem hi)) heK (fun i hi=> h' i (mem_insert_of_mem hi))) (D:=∏ i∈F,v i) (C:=v i) (he i (mem_insert_self ..)); intro U; rw [norm_prod]; exact prod_le_prod (fun _ _=> norm_nonneg _) fun i hi=> heK _ hi U
lemma variations {f : ℝ→ A→ℝ} (a:ℝ) (h : Varies f x s): Varies (fun x U=> a * f x U) x s:= by
  intro e he; have hv : 0 < |a|+1:=add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
  let p:= e / (|a|+1)
  filter_upwards [h p (div_pos he hv)] with y hy U; rw [← mul_sub,norm_mul]; rw [← div_mul_cancel₀ e hv.ne']; exact mul_le_mul (b:=(|a|+1)) (le_add_of_nonneg_right zero_le_one) (hy U) (norm_nonneg _) hv.le |>.trans_eq (mul_comm (|a|+1) p) -- rw problem
lemma choirA {f:ℝ → Trio.Offer G c} (h:∀ i,Varies (fun x=>f x i) x s) (i:Door c): Varies (fun x=> choir (-f x) i) x s:= by
  have ht: Varies (fun x=> (f x i.2) ∘ i.1.view) x s:= fun e he=> (h i.2 e he).mono fun y hy U=> hy _
  exact variations _ ht.neg
section ward
variable {V:ℝ→ Collection.Source G c} {g t: ℝ → Trio.Offer G c}
   {p k : ℕ→ℝ} (hp : ∀ x∈s,∀ i,B.Regular (neighbors z i) (g x i))
    (ht:∀ x∈s,∀ i,B.supBounds i (neighbors z i) (g x i) a)
    (hc:∀ x∈s,∀ i U,‖t x i U‖ ≤ d)
local notation "Z" => (Marlin.lodge X z w)
local notation "D" => (fun x=> Marlin.bison (V x) (g x) (t x))
local notation "🥁" => (fun x=> Marlin.poursP B Z (D x))
variable (H:Compared X B V s) (hy:∀ x∈s,∀ i ε, 0<ε→ ∀ᶠ y in 𝓝[s] x,variesRegular B (leap z i) (g x i) (g y i) ε) (hz:∀ x∈s,∀ i,Varies (fun y=>t y i) x s)
include H hp ht hc hy hz
lemma tune (hn : ∀ x∈s,∃ u:ℕ→ℝ,∀ i V', ‖(V x).hardRead i V'‖ ≤ u i): Compared (Marlin.pluck B Z) B 🥁 s:= by
  constructor
  · intro x hx; constructor
    · intro i ε hε
      suffices he:∀ i:Civ c,∀ᶠ y in 𝓝[s] x,variesRegular B (Sum.elim X.reg (sea z) i) (Sum.elim (V x).logRead (Song.choir (g x)) i) (Sum.elim (V y).logRead (Song.choir (g y)) i) ε from he _
      rintro (i|i)
      · exact (H.values x hx).1 i ε hε
      have ht θ (f f':Trio.Offer G c) (i:Site c) (p: ℝ) (h : B.Regular (neighbors z i) (f i)) (h' : B.Regular (neighbors z i) (f' i)) (hp:variesRegular B (leap z i) (f i) (f' i) p) (he:Rim c*(turnFee B*p)≤ ε): variesRegular B (sea z (θ,i)) (choir f (θ,i)) (choir f' (θ,i)) ε := by
        have hp':= CouplingShape.sup_scale (Rim c) (Song.transSup θ (VerifiedReset.reg_sub h h') ((VerifiedReset.sup_varies (d:=leap z i) h h').mp hp))
        rw [abs_of_nonneg (rim_nn _)] at hp'; apply (sup_varies (CouplingShape.reg_scale (Rim c) (θ.regular (G:=G) (X:= (leap z i).support) h)) (CouplingShape.reg_scale (Rim c) (θ.regular h'))).2
        refine VerifiedReset.sup_le ?_ he; dsimp only; rw [show (Rim c) • ((f i) ∘ Seat.view θ) - _= Rim c • ((f i-f' i) ∘ θ.view) from ?_] -- θ ret Type?
        · exact hp'
        ext U; apply Eq.symm; apply mul_sub ..
      let b:= Rim c * turnFee B; have hb : 0<b:=mul_pos (inv_pos.mpr (by positivity)) (turnFee_pos _)
      let r:=ε/b; filter_upwards [hy _ hx i.2 r (div_pos hε hb),self_mem_nhdsWithin] with y hy hu
      exact ht i.1 (g x) (g y) i.2 r (hp _ hx _) (hp _ hu _) hy (le_of_eq (by rw [← mul_assoc]; unfold r; change b* (ε / b)= ε; field_simp))
    intro i; obtain ⟨u,hu⟩:= hn x hx
    have hV i: Varies (fun x=> (D x).logarithm i) x s:= by
      change Varies (fun x=> Sum.elim (fun _=>0) (choir (- t x)) (leanU c i)) x s; cases he: leanU c i
      · exact Varies.fixed 0
      exact choirA (hz x hx) _
    let p:= Rim c*d; have hl:Rim c *d≥0:=mul_nonneg (rim_nn _) ((norm_nonneg _).trans (hc _ hx 0 1))
    have ht i U:Real.exp ((D x).logarithm i U) ≤ Real.exp p:= by
      apply Real.exp_monotone (le_trans (le_abs_self _) ((Marlin.softly _ (t x) _ (hc _ hx) _ i U).trans ?_))
      cases leanU c i; exact hl; exact le_rfl
    have hH i : Varies (fun y V=>Pipes.reach (D y) i V) x s:= by
      cases i
      · exact (H.values _ hx).2 _
      next i=> exact (Varies.exp (hV i) (ht i) (Real.exp_pos p)).sub (Varies.fixed (fun _=>1))
    let v : Ovens.Label→ℝ:= Sum.elim u (fun _=> Real.exp p+1)
    have he i U: ‖reach (D x) i U‖≤v i:= by
      cases i; exact hu _ _
      next i=> exact (norm_sub_le ..).trans (add_le_add ((Real.norm_of_nonneg (Real.exp_nonneg _)).trans_le (ht i U)) norm_one.le)
    let f y V:= ∏ j∈(hak Z i).val,Pipes.reach (D y) j V
    intro ε hε; filter_upwards [productsA (hak Z i).val v (fun i _=> hH i) (fun i _=> he i) ε hε] with y hy U
    change ‖solid (hak Z) B (D x) i U-solid (hak Z) B (D y) i U‖ ≤ _; unfold solid; split; exact hy U; simpa only [sub_zero,norm_zero] using hε.le
  intro x hx y hy
  obtain ⟨r,e,b,h,H',hp',hq,hy'⟩:= H.series x hx y hy
  obtain ⟨h₀,h₁,h2,h3,h4,h5⟩:= gatheredCrew z w (x:=x) hp ht hc hx (hy.comp h|>.eventually self_mem_nhdsWithin) H' hp' hq hy'
  exact ⟨r,h₀,h₁,h,h2,h3,h4,h5⟩
end ward
end YM.PhysicalNext.Repeat.Shingle
