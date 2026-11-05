import YM.MergeProof.Stage
import YM.FullVolume.Florid.HeatR
import YM.FullVolume.Sym.Able
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
open ConnectedActivityE6.Empire.Imago Crew Mallow Extra.Iteration Ovens Ovens.Pipes Progress.DirectedRecipe Rack FullVolume.Ray.Weigh
variable {G:Gauge}{c:Side}{m:ℕ}{X:Pipes G c}{P:BudgetPoint}{φ κ η v γ:ℝ}{A:Type}[Fintype A]
    (Z : ℕ≃ X.Pellet)(f:sun→ℝ→Finset A→Tap G c){V:sun→Tap G c} (hp:1≤v)
    (hf:Kit (fun i=>(X.kernel i).support) v γ (fun i x y=> (f i x y).forced) P.B (P.supportExponent+1)) (hV:league X.softer P.B (Tap.logarithm ∘ V) (P.supportExponent+1) v η) (hr:Payments.Rates P.B φ γ η κ)
    (hw:∀ t x y,(f t x y).logarithm=(V t).logarithm)
include hf hV hr hw hp
lemma seasons : Kit (fun i=> (Ovens.Pipes.addr Z P i).support) v φ (fun i x y=> solid Z P (f i x y)) P.B P.supportExponent :=by
  obtain ⟨f',hK,hx⟩:= hf; obtain ⟨p,hP,hs⟩:= hV
  let v':= Real.exp (-κ); let D (i:Ovens.Label):ℝ:= i.elim (fun _=>v') (fun _=>1)
  let F : Ovens.Label→ℝ:=Sum.elim (fun i=> Real.exp κ*f' i) (fun i=> 2*p i)
  have hA : Ac.Hit X.patch P.B F (P.supportExponent+1) (Payments.inflation γ η κ):= by
    intro i; exact Cost.sum (hitC _ _ _ hK (Real.exp_nonneg _) i) (hitC _ _ _ hP zero_le_two i)
  have hb : 0≤v' := (Real.exp_pos _).le; have hD i:0≤ D i:=by cases i; exact hb; exact zero_le_one
  have hM i:0≤ F i:= by cases i; exact mul_nonneg (Real.exp_nonneg _) (hx _|>.toll); exact mul_nonneg zero_le_two (hs _ (1:Config G c)|>.nonneg)
  have hY i:D i ≤ 1:= by cases i; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.heading); rfl
  let w(i)(x:sun)(U:Config G c)(p:ℝ)(t:Finset A):= reach (f x p t) i U
  have hh i:Strung (w i) v (D i*F i):=by
    rcases i with i|i
    · apply (hx i).tame; change f' i ≤ v'*(Real.exp κ*f' i); rw [← mul_assoc, ← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
    change Strung _ v (1*(2*p i)); rw [one_mul]; let x(t:sun) U:=Real.exp ((V t).logarithm i U)-1
    rw [show w (.inr i) = fun t U j k=> x t U from funext fun t=> funext fun U=>funext fun j=> funext fun k=> by change Real.exp ((f _ _ _).logarithm i U)-1= _;rw [hw] ]
    have he U:Scout v (phraseS fun t=> x t U) (2*p i):=by
      apply (hs i U).burn.enlarged
      obtain ⟨x,hZ⟩:= X.sites i; have ht:= budget_single (hP x) i; rw [if_pos hZ] at ht
      have hW:= (hs i U).nonneg
      have hh: |p i| ≤1:= (abs_of_nonneg hW).trans_le ((le_mul_of_one_le_right hW (Real.one_le_exp (mul_nonneg (add_nonneg P.exponent_pos.le zero_le_one) (Nat.cast_nonneg _)))).trans (ht.trans hr.soft_limit))
      exact (le_abs_self _).trans ((Real.abs_exp_sub_one_le hh).trans_eq (congr_arg (fun x:ℝ=>2*x) (abs_of_nonneg hW)))
    exact Strung.foyer hp (he 1|>.nonneg) he
  let E (i:ℕ):=(Z i).val; let b i:=v' *∏ j∈ E i,F j
  have hc:= hr.capital; have ht:= Ac.forest X.patch P.B P.exponent_pos.le hM hA hc (budget_nonneg (hA 0))
  refine ⟨b,?_,fun i=>?_⟩
  · intro i; let d (x:ℕ):= v'*Ac.roots X.patch P.B F P.supportExponent i (E x)
    have he := budget_loosen (Cost.scale (budget_pull E (Subtype.val_injective.comp Z.injective) (ht i)) v' hb) hr.returns
    have hh j : (if i∈ (Ovens.Pipes.addr Z P j).support then b j*Real.exp (P.supportExponent*coverNumber P.B (Ovens.Pipes.addr Z P j).support) else 0)=d j:= by
      have hJ := (Z j).property; let s:=E j; have ht: (Ovens.Pipes.addr Z P j).support=s.biUnion X.patch:= rfl
      rw [ht]; split
      next ht=> unfold d; rw [Ac.roots, if_pos (show Ac.Spark X.patch (E j)∧ _ from ⟨hJ.2.1,ht⟩)]; unfold b; unfold s; ring
      next ht=> unfold d; rw [Ac.roots, if_neg (show ¬(Ac.Spark X.patch (E j) ∧ _) from fun h=> ht h.2),mul_zero]
    exact (funext hh) ▸ (show SumBudget d φ from he)
  let u:= E i; have ht: 0≤∏ j∈E i,F j:= prod_nonneg fun i _=> hM i
  have htG:= Strung.winds u w _ hp (fun i _=> hh i)
  have hS:∀ i (hi:i∈u),0 ≤ D i* F i:= fun i _=> mul_nonneg (hD i) (hM i)
  let g:= ∏ j∈u,w j; rw [show Sounding (fun i x y=> solid Z P (f i x y)) i = fun t U=> if (addr Z P i).eligible P.threshold U then g t U else 0 from ?_]
  · refine Strung.cloud (Strung.tame htG ?_) _
    obtain ⟨j,hj⟩:= (Z i).property.1; change (∏ i∈u,D i*F i)≤ _; rw [prod_mul_distrib]; apply mul_le_mul_of_nonneg_right _ ht; change ∏ j∈u,D j ≤ _
    exact (Finset.prod_le_prod_of_subset_of_le_one (show {Sum.inl j}⊆u from singleton_subset_iff.mpr (mem_toLeft.mp hj)) (fun i _=>hD i) (fun i _ _=>hY i)).trans_eq (Finset.prod_singleton ..)
  ext t U x y; unfold Sounding solid g; dsimp only; split_ifs; swap; · rfl
  simp_rw [Finset.prod_apply]; rfl
end YM.PhysicalNext.Repeat.Jams
