import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Vested
/-! # exp derivation on compulsory multiple pieces Restores. Doesn't combine absolute
 budgets into forbidden ξ uptake; uses ALL submissions in budget.
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
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f}
    {x μ C v e d D : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W x μ L Q o C T R}
variable (Θ : Year H j v χ)
include Θ

lemma noses : ∃ M : ℝ,0 ≤ M ∧∃ s : ℝ,0<s∧ s ≤ 1 ∧∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ),Equalized Q.table R I a b t→ t ≤ s →0<t →∀ (H':Cash W x μ L Q o C T I),Year H' j v χ→∀ (X:Match.Alliance H H' 1 0), X.units= Equiv.refl _→
   ∃ f:H.Chapter→ℝ, SumBudget f M ∧∀ p U, |H'.colognePool χ U (X.editor p)- H.colognePool χ U p| ≤ t*f p := by
  obtain ⟨K,hK,s,hs,h⟩:= eventide Θ; obtain ⟨M,hM,hY⟩:= masterP H Θ.year.holds
  have hb:= H.laws.intake.positive
  refine ⟨M+K,add_nonneg hM hK,min s (min (1/4) (R.beta/2)),lt_min hs (lt_min (by norm_num) (by positivity)),(min_le_right ..).trans ((min_le_left ..).trans (by norm_num)),?_⟩; intro I a b t hp he hy H' hx X hQ
  have he' := he.trans (min_le_right ..); obtain ⟨k,h',hk⟩:= hY I a b t hp hy (he'.trans (min_le_left ..)) (he'.trans (min_le_right ..)); obtain ⟨f',hf,ht⟩:= h I a b t hp (he.trans (min_le_left ..)) hy H' hx X hQ
  let D (p:H.Chapter):=Sum.elim (k ∘ Subtype.val) f' p; refine ⟨D,Extra.Iteration.Cost.sum (f:=D) (budget_pull Subtype.val Subtype.val_injective h') hf,?_⟩; intro p U
  rcases p with p|p
  · change |H'.depositsPool χ U (X.honoring p)-H.depositsPool χ U p|≤ _
    unfold Cash.depositsPool Cash.spawn; rw [show (X.honoring p).val=p.val from congr_arg (fun e:Molecule S≃_=> e p.val) hQ]
    letI:Nonempty (Tree.Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
    let X i:= prism T x χ o.K U (Greenbelt.allot (S:=S) i)
    let Y i:= H'.emerging (X i) p.val; let Q' i:= H.emerging (X i) p.val
    change |likely Y-likely Q'| ≤ _
    rw [show likely Y -likely Q'=likely (fun i=> Y i-Q' i) from (by unfold likely; dsimp only; rw [← mul_sub,sum_sub_distrib])]; exact Cash.poleIncome (fun i=> Y i-Q' i) _ fun i=> hk _ H' _ (X i) rfl rfl p.val
  let V:= Pressure.temp x; have hZ : Captain.reachability (H:=H') (X.furrow p)= Song.perf H p:= (Song.reconnects ..).symm
  change |-H'.trainedPool χ U (X.furrow p)- -H.trainedPool χ U p| ≤ t*f' p; rw [neg_sub_neg,abs_sub_comm]
  have ht' (p : H.fragrances):H.trainedPool χ U p=_:= congr_fun ((Θ.net.permitAverage p).2.2.2.1) U
  rw [ht',congr_fun (((hx.net.permitAverage (X.furrow p)).2.2.2.1)) U, show unionOf H'.smallAt (X.furrow p).snd= Song.perf H p from hZ]
  by_cases hm : Healthy V (Song.perf H p) U
  · rw [masked_eq _ _ _ _ hm, masked_eq _ _ _ _ hm]
    exact (ht p U hm ℝ (fun _=>U) 0 rfl (show Mode (fun _:ℝ=> U) (0:ℝ) j v from ⟨Θ.net.position.le,fun i=> a_oneB G _ Θ.net.position.le⟩)).bound
  rw [masked_ne _ _ _ _ hm, masked_ne _ _ _ _ hm,sub_self,abs_zero]; exact mul_nonneg hy.le (hf.1 _)
omit Θ in
lemma stood (H : Cash W x μ L Q o C T R) (h : Cash.Renewed n e d D H) :
   let k:= OmitClusters.grade H.seam (H.thinPay n) (H.broadPay n)
   Summable k ∧∀ (χ:Chi) i V, |H.colognePool χ V i|≤ k i:= by
  intro k
  have he := Gas.absolute H.seam (H.thinPay n) _ (radiusB x) H.testS (fun i=> i.2.1) (add_nonneg h.full h.post.le) (show Ready _ _ _ _ (Q.overture L μ x n) d (1/2) from ?_)
  swap
  · simp_rw [Real.norm_of_nonneg ((show ∀ i:H.ThinP,0≤ H.thinPay n i from fun i=>H.ours_pos ..) _)] -- parse
    exact h.shift
  let v i:=‖Gas.term H.seam (H.thinPay n) i‖
  have hp i : v i=k (.inr i):= by unfold v; rw [Gas.term_nonneg]; simp_rw [Real.norm_of_nonneg ((show ∀ i:H.ThinP,0≤ H.thinPay n i from fun i=>H.ours_pos ..) _)]; rfl
  have hx (i:H.ThickP) : 0≤ H.broadPay n i := H.ours_pos ..
  have hu:= AbsoluteSums.Product.everyone_ne _ _ hx (fun i _=> i.2.1) h.marks
  have hz := hu.2.1.of_nonneg_of_le hx (fun i=> le_mul_of_one_le_right (hx i) (Real.one_le_exp (mul_nonneg (add_nonneg h.full h.post.le) (Nat.cast_nonneg _))))
  refine ⟨(HasSum.sum (f:=k) hz.hasSum (show HasSum _ (∑' i,v i) from (funext hp) ▸ (show Summable v from he.2.1).hasSum)).summable,?_⟩ -- dependent?
  intro χ i V
  rcases i with i|i
  · exact (H.renew χ V n).2 i
  change ‖-(Gas.term _ _ i)‖ ≤ _; rw [norm_neg,Gas.term_nonneg]; apply div_le_div_of_nonneg_right _ (by positivity); apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); exact Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun _ _=>(H.renew χ V n).1 _)

lemma faces (h : Cash.Renewed n e d D H) : ∃ M : ℝ,0 ≤ M ∧∃ s : ℝ,0<s∧∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ),Equalized Q.table R I a b t→ t ≤ s →0<t →∀ (H':Cash W x μ L Q o C T I),Year H' j v χ→∀ (X:Match.Alliance H H' 1 0), X.units= Equiv.refl _→
   ∃ f:H.Chainbook→ℝ, SumBudget f M ∧∀ p U, |H'.smilesPool χ U (X.tongs p)- H.smilesPool χ U p| ≤ t*f p := by
  obtain ⟨K,hK,s,hs,he,hV⟩:= noses Θ; let k:=OmitClusters.grade H.seam (H.thinPay n) (H.broadPay n); let v:= ∑' i,k i; have hk:= stood H h
  refine ⟨Real.exp (v+K),Real.exp_nonneg _,s,hs,?_⟩; intro I a b t hp ht hF H' Θ' X hz; obtain ⟨f',hf,hx⟩:= hV I a b t hp ht hF H' Θ' X hz
  let F (p:H.Chapter):= k p+f' p; have hd : SumBudget F (v+K):= budget_plus ⟨H.thick_pos n,hk.1,le_rfl⟩ hf
  have he' := concert hd.2.1
  refine ⟨manyW F,⟨manyW_nonneg hd.1,he'.summable,he'.tsum_eq.trans_le (Real.exp_le_exp.mpr hd.2.2)⟩,?_⟩; intro p U; have hp:X.units=Equiv.refl _:=hz
  have hU:pull 1 0 U=U := by rw [pull_one]; funext; simp [Lattice.translate]
  unfold Cash.smilesPool; split
  next hh =>
    have hp' : H.Fresh p∧Ac.Spark H.bookFoot p.1∧H.statesPool U p:= by refine ⟨(X.sap p).2 hh.1,(X.splint p).2 hh.2.1,?_⟩; have he := (X.festoon U p).2 hh.2.2; rw [hU] at he; exact he
    rw [if_pos hp',← cashes X.editor (fun p=> H'.colognePool χ U (X.editor p)) _ (fun _=> rfl) p]; exact license _ _ k f' hF.le (ht.trans he) (hk.2 χ · U) (fun i=> hx i U) hf.1 p
  next hh =>
    have he : ¬(H.Fresh p∧Ac.Spark H.bookFoot p.fst∧H.statesPool U p):= fun hx => hh ⟨(X.sap p).1 hx.1,(X.splint p).1 hx.2.1,(X.festoon U p).1 (by rw [hU]; exact hx.2.2)⟩
    rw [if_neg he,sub_self,abs_zero]; exact mul_nonneg hF.le (manyW_nonneg hd.1 p)
end YM.PhysicalNext.Repeat.Yearling
