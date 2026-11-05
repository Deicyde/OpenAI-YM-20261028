import YM.FullVolume.Sym.Stage
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable {P:BudgetPoint}
variable {v δ e b γ B η:ℝ} {n d:ℕ} {C:Tune H v δ}
/-! H02 pricing actual pellets, retained for use after interpolation. No Borel jet probes off their committed tracks. -/
open Progress.DirectedRecipe Ovens Ovens.Pipes Marlin
section calcz
variable {m : ℕ} {φ κ : ℝ} {X: Pipes G c} (Z : ℕ≃ X.Pellet)
    (f:sun→Tap G c) (hp:1≤v) (h:league (fun i=> (X.kernel i).support) P.B (Tap.forced ∘ f) (P.supportExponent+1) v γ)
    (hs:league X.softer P.B (Tap.logarithm ∘ f) (P.supportExponent+1) v η) (hr:Payments.Rates P.B φ γ η κ)
-- explicit dependencies for fusion cost
lemma hitC {ι:Type} {e u C:ℝ} (j:ℕ)(f:ι→Support c)(a:ι→ℝ)(h:Ac.Hit f j a e u)(he:0≤C) : Ac.Hit f j (fun i=> C*a i) e (C*u):=by
  intro i; convert Cost.scale (h i) C he using 2 with k; split<;>ring
lemma meetC {ι:Type} {p:ℝ} (V:Finset ι) (f:ι→ℝ→ℝ)(k:ι→ℝ)(he:1≤p) (h: ∀ i∈V,Scout p (f i) (k i)): Scout p (fun x=> ∏ i∈V,f i x) (∏ i∈V,k i):=by
  induction V using Finset.induction_on with
  | empty =>simpa using! Scout.still he (1:ℝ)
  | insert i s hi ih =>simp_rw [prod_insert hi]; exact (h i (by simp)).multiplies (ih fun i hi=> h i (mem_insert_of_mem hi))
include h hs hr hp
lemma venture : league (fun i=> (Ovens.Pipes.addr Z P i).support) P.B (fun i=> solid Z P (f i)) P.supportExponent v φ :=by
  obtain ⟨f',hK,hx⟩:= h; obtain ⟨p,hP,hV⟩:= hs
  let v':= Real.exp (-κ); let D (i:Ovens.Label):ℝ:= i.elim (fun _=>v') (fun _=>1)
  let F : Ovens.Label→ℝ:=Sum.elim (fun i=> Real.exp κ*f' i) (fun i=> 2*p i)
  have hA : Ac.Hit X.patch P.B F (P.supportExponent+1) (Payments.inflation γ η κ):= by
    intro i; exact Cost.sum (hitC _ _ _ hK (Real.exp_nonneg _) i) (hitC _ _ _ hP zero_le_two i)
  have hb : 0≤v' := (Real.exp_pos _).le; have hD i:0≤ D i:=by cases i; exact hb; exact zero_le_one
  have hM i:0≤ F i:= by cases i; exact mul_nonneg (Real.exp_nonneg _) (hx _ (1:Config G c)|>.nonneg); exact mul_nonneg zero_le_two (hV _ (1:Config G c)|>.nonneg)
  have hY i:D i ≤ 1:= by cases i; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.heading); rfl
  have hh i U:Scout v (fun x=> reach (f (pinch x)) i U) (D i*F i):=by
    rcases i with i|i
    · apply (hx i U).enlarged; change f' i ≤ v'*(Real.exp κ*f' i); rw [← mul_assoc, ← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul] -- unfold
    change Scout v _ (1*(2*p i)); rw [one_mul]; apply (hV i U).burn.enlarged
    obtain ⟨x,hZ⟩:= X.sites i; have ht:= budget_single (hP x) i; rw [if_pos hZ] at ht
    have hW:= (hV i U).nonneg
    have hh: |p i| ≤1:= (abs_of_nonneg hW).trans_le ((le_mul_of_one_le_right hW (Real.one_le_exp (mul_nonneg (add_nonneg P.exponent_pos.le zero_le_one) (Nat.cast_nonneg _)))).trans (ht.trans hr.soft_limit))
    exact (le_abs_self _).trans ((Real.abs_exp_sub_one_le hh).trans_eq (congr_arg (fun x:ℝ=>2*x) (abs_of_nonneg hW)))
  let E (i:ℕ):=(Z i).val; let b i:=v' *∏ j∈ E i,F j
  have hc:= hr.capital; have ht:= Ac.forest X.patch P.B P.exponent_pos.le hM hA hc (budget_nonneg (hA 0))
  refine ⟨b,?_,fun i U=>?_⟩
  · intro i; let d (x:ℕ):= v'*Ac.roots X.patch P.B F P.supportExponent i (E x)
    have he := budget_loosen (Cost.scale (budget_pull E (Subtype.val_injective.comp Z.injective) (ht i)) v' hb) hr.returns
    have hh j : (if i∈ (Ovens.Pipes.addr Z P j).support then b j*Real.exp (P.supportExponent*coverNumber P.B (Ovens.Pipes.addr Z P j).support) else 0)=d j:= by
      have hJ := (Z j).property; let s:=E j; have ht: (Ovens.Pipes.addr Z P j).support=s.biUnion X.patch:= rfl
      rw [ht]; split
      next ht=> unfold d; rw [Ac.roots, if_pos (show Ac.Spark X.patch (E j)∧ _ from ⟨hJ.2.1,ht⟩)]; unfold b; unfold s; ring
      next ht=> unfold d; rw [Ac.roots, if_neg (show ¬(Ac.Spark X.patch (E j) ∧ _) from fun h=> ht h.2),mul_zero]
    exact (funext hh) ▸ (show SumBudget d φ from he)
  let u:= E i; have ht: 0≤∏ j∈E i,F j:= prod_nonneg fun i _=> hM i
  by_cases hK:(Ovens.Pipes.addr Z P i).eligible P.threshold U
  · have hf (x:ℝ): phraseS (fun j=> solid Z P (f j) i U) x= ∏ j∈u,reach (f (pinch x)) j U:= if_pos hK
    refine ((meetC u (fun j x=> reach (f (pinch x)) j U) _ hp (fun i _=> hh i _)).replace (fun x hx=> (hf x).symm)).enlarged ?_
    obtain ⟨j,hj⟩:= (Z i).property.1; rw [prod_mul_distrib]; apply mul_le_mul_of_nonneg_right _ ht; change ∏ j∈u,D j ≤ _
    exact (prod_le_prod_of_subset_of_le_one (show {Sum.inl j}⊆u from singleton_subset_iff.mpr (mem_toLeft.mp hj)) (fun i _=>hD i) (fun i _ _=>hY i)).trans_eq (prod_singleton ..)
  exact ((Scout.still hp (0:ℝ)).replace (fun x hx=> Eq.symm (if_neg hK))).enlarged ((norm_zero).trans_le (mul_nonneg hb ht)) -- eq
end calcz
end YM.PhysicalNext.Repeat.Jams
