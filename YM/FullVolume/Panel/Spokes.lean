import YM.FullVolume.Mark.Sight
/-! Real-linear on the priced germs. Use *actual open neighborhoods* of the base so includes full ordered derivatives at Healthy =, and on path arrays with history-specific conventions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{R E : Rep G n}{Y:Hol G} {κ a b t e u w c σ v:ℝ} {Z : Support n} {B: SectionData F} {ι:Type}
def Sculpts (B:BudgetPoint) (Z : Support n) (f g: Config G n→ℂ) := ∀ U,Healthy B.threshold Z U→ f ∘ increment U=ᶠ[𝓝 0] g ∘ increment U
namespace Sculpts
variable {P:BudgetPoint}{f g : Config G n→ℂ}(h:Sculpts P Z f g)
include h
lemma sculpt (V): masked P.threshold Z f V= masked P.threshold Z g V:=by
   by_cases he:Healthy P.threshold Z V<;>simp [he]
   exact Push.Local.left_congr [] _ (h V he)
lemma weights (hr:f |> P.Regular Z)(hz: P.Regular Z g)(hk:d ≤ P.order) : weighted Y F 0 Z P.threshold f=weighted Y F 0 Z P.threshold g:=by
   have hp := h (1:Config G n) (one_healthy _ _ P.threshold_pos.le); unfold weighted
   apply congr_arg (F.scaled _); apply congr_arg F.coords
   let o: Site n:=0; let W:=project Y o Z g d; have hw: Reads Y o Z W g:= project_reads Y o hz hk
   apply project_eq; change Reads Y o Z W f
   by_cases he:Nonwrapping Z o; swap; · rw [Reads,if_neg he] at *; rw [hw,show g 1 =f 1 from (Push.Local.left_congr [] _ hp).symm]
   rw [Reads,if_pos he] at *
   intro J; let p:=testLog Y d o J; let P₀:= Y.testLinks d o J; let Q₀:= (increment (1:Config G n)) ∘ p
   have hf : f ∘ P₀=ᶠ[𝓝 0] g ∘ P₀:=by
      have hT:Tendsto p (𝓝 0) (𝓝 0):=by
          have hz:= (testLog_diff Y d o J).continuousAt.tendsto; rw [testLog_zero] at hz;exact hz
      have hQ : P₀=ᶠ[𝓝 0] Q₀:= increment_testLog .. -- edit
      exact (hQ.fun_comp f).trans ((hp.comp_tendsto hT).trans (hQ.symm.fun_comp g))
   obtain ⟨hi,hL,hv⟩:=hw J; exact ⟨hi.congr_of_eventuallyEq hf,hL,fun k hk=>(hf.iteratedDeriv_eq (n:=k)).trans (hv k hk)⟩
end Sculpts
section sum
variable {ι:Type}{x:ι→Pin F n}{y:ι→ℂ}{f:ι→ Config G n→ℂ}{Q:BudgetPoint} (a₀:Finset ι)
lemma formatPin_sum (h:∀ i,(tell (x i)).Format 0 Y R): (tell (∑ i∈a₀,y i • x i)).Format 0 Y R:=by
    induction a₀ using Finset.induction_on with
    | empty=>
       rw [sum_empty]; exact ⟨fun i=>(regular0 R.p _ (0:Site n)).1,fun i=>spot _ i,fun i=>rfl,fun _ _=> vanishing0 _ _ Y,fun i U h=>(h rfl).elim,fun i h=>(h rfl).elim,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
    | @insert i S hx ih=>
       rw [sum_insert hx]; exact formatK F _ _ (format_add F _ _ (stretch_format (y i) (h i) : (book _ (y i •(x i).2)).Format ..) (show (book ..).Format _ _ _ from ih)) -- display
lemma sum_weigh (h:∀ i,Q.Regular Z (f i))(hd:d ≤ Q.order): Q.Regular Z (∑ j∈a₀,y j • f j) ∧ weighted Y F 0 Z Q.threshold (∑ i∈a₀,y i • f i)=∑ i∈a₀,y i • weighted Y F 0 Z Q.threshold (f i):=by
    unfold weighted
    induction a₀ using Finset.induction_on with
    | empty=> rw [sum_empty,sum_empty]; exact ⟨(regular0 Q Z 0).1, by rw [project_zero,map_zero,map_zero]⟩
    | @insert i s hi ih=>
       have hz:= regular_smul (y i) (h i); rw [sum_insert hi,sum_insert hi]; rw [Local.project_add _ _ hz ih.1 hd,project_smul Y _ _ (h i) hd,map_add,map_smul,map_add,map_smul,ih.2]; exact ⟨regular_add hz ih.1,rfl⟩
end sum
section pack
variable {S:ℕ→Support n}{M: Local.Raw F n}{P:ι→ Local.Raw F n}
structure Have (R:Rep G n) (X:Local.Raw F n) (S:ℕ→Support n)(B: SectionData F)(Y:Hol G)(w u κ:ℝ):Prop where
   format : X.Format 0 S R
   wage:∃ a b c:ℝ,Tare X 0 S Y B R w u κ a b c
abbrev gala (K:Keeper R.p R.activities)(B:SectionData F)(Y:Hol G)(M:Local.Raw F n)(S:ℕ→Support n):= closeK K (mint (K.supply (fun i=>joint B 0 (S i))) M Y)
variable (K:Keeper R.p R.activities)(y:ι→ℂ) (hp: R.Lawful a b c v u)(hk:0<κ) (hH:Readable Y B R.p n w) (hM:Have R M S B Y w u κ)(hP:∀ i,Have R (P i) S B Y w u κ)
include hp hk hH hM hP
local notation "T"=> K.supply (fun i=>joint B 0 (S i))
local notation "D"=> R.p
lemma trustK [Fintype ι] (hA:∀ i,Sculpts R.p (S i) (M.bulk i) (∑ j,y j • (P j).bulk i)) (hx:M.seed=∑ i,y i • (P i).seed)(hv : M.forced = ∑ i,y i • (P i).forced):
     let U:=∑ i,y i • gala K B Y (P i) S; (tell U).Format 0 Y R ∧ Pros U (gala K B Y M S) R.p:=by
    intro U; let A:= mint T M Y; let A' i:= mint T (P i) Y
    let x i:=gala K B Y (P i) S
    have hc(i): (tell (x i)).Format 0 Y R:= invest (A' i) K (usage T (hP i).format hp hH)
    have he(i):= sum_weigh (f:=fun j=>(P j).bulk i) (y:=y) (Y:=Y) (F:=F) univ (fun j=>(hP j).format.regular i) hH.order; let g j i:= (P j).row 0 S Y R.p.threshold i
    have hg i:M.row 0 S Y R.p.threshold i=∑ j,y j • g j i:= (Sculpts.weights (hA i) (hM.format.regular _) ((he i).1) hH.order).trans (he i|>.2)
    have hP₀ : ∀ i,Sculpts R.p (joint B 0 (S i)) (A.regular i) (∑ j,y j • (A' j).regular i):=by
       intro i V hz
       let p (a:F.Coeff):Config G n→ℂ:= Local.presented B 0 R.p.threshold a
       have hv' : p (M.row 0 S Y R.p.threshold i)=∑ j,y j • p (g j i):=by unfold p; rw [hg i,map_sum]; simp only [map_smul]
       filter_upwards [hA i V (Finset.disjoint_of_subset_left Finset.subset_union_left hz)] with W h
       let z:=increment V W; change M.bulk i z-p (M.row 0 S Y R.p.threshold i) z=_; rw [show M.bulk i z=_ from h,hv',Function.comp_apply,Finset.sum_apply, Finset.sum_apply,Function.comp_apply,Finset.sum_apply, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; change y j • _ - y j • _=y j • ( (P j).bulk i z- p (g j i) z); exact (smul_sub ..).symm
    have hP₁ : ∀ i, rebate Y B 0 (S i) R.p.threshold (M.bulk i)=∑ j,y j • rebate Y B 0 (S i) R.p.threshold ((P j).bulk i):=by
       intro i; let M'(u:Config G n→ℂ):= maskLinear R.p.threshold (S i) u; let J:=joint B 0 (S i)
       have h₁:M' (M.bulk i)=∑ j,y j • M' ((P j).bulk i):=by
           unfold M'; rw [show maskLinear R.p.threshold (S i) (M.bulk i)= _ from funext (hA i|>.sculpt)]; change maskLinear _ _ (∑ _, _)= _; rw [map_sum]; simp_rw [map_smul]
       let g₀:= maskLinear (G:=G) R.p.threshold J
       have h₂:g₀ (A.regular i)=∑ j,y j • g₀ ((A' j).regular i):=by rw [show g₀ (A.regular i)=g₀ _ from funext ((hP₀ i).sculpt)]; rw [map_sum];simp_rw [map_smul]
       let t:= Local.primary B (0:Site n) R.p.threshold; change M' (M.bulk i)- t (M.row 0 S Y _ i)-g₀ (A.regular i)=∑ j,y j • (M' ((P j).bulk i)-t (g j i)-g₀ ((A' j).regular i)); rw [h₁,hg i,map_sum,h₂]; simp only [map_smul,smul_sub,sum_sub_distrib]

    choose a₁ b₁ c₁ hx' using fun i=> (hP i).wage; obtain ⟨x₁,y₁,z₁,hT⟩:= hM.wage
    let t:= R.p.threshold
    have hy k: Summable (fun i=> g k i):= (Size.series _ ((hx' k).row_cost hH (hP k).format |>.2.1)).of_norm
    have hK : profile R.activities A.forced= ∑ i,y i • profile R.activities (A' i).forced:=by
       have he:= budgetProfile T hT hM.format hH hp hk; rw [show profile R.activities A.forced= _ from he]; simp_rw [fun i=>show profile R.activities (A' i).forced= _ from budgetProfile T (hx' i) (hP i).format hH hp hk]; simp_rw [smul_add,sum_add_distrib]; apply congr_arg₂ (·+·)
       · rw [hv]; funext i V; simp_rw [← profile_scale]; unfold profile cram; simp_rw [Finset.sum_apply]; rw [Summable.tsum_finsetSum _ ]; intro j _; simp only [Pi.smul_apply,smul_eq_mul]; exact (((limb (hx' j|>.packets)).summable V).comp_injective Subtype.val_injective).mul_left _
       -- linear hooks. tsum finite terms
       let U:Response G n:=clipSum (fun i=> joint B 0 (S i)) (fun i=> rebate Y B 0 (S i) t (M.bulk i)); let V j:Response G n:= clipSum (fun i=>joint B 0 (S i)) (fun i=> rebate Y B 0 (S i) t ((P j).bulk i))
       have hV : U=∑ j,y j • V j:=by
           funext i K; unfold U t; simp_rw [hP₁]; unfold V clipSum cram; simp_rw [Finset.sum_apply,Pi.smul_apply, smul_eq_mul]; rw [Summable.tsum_finsetSum _ ]; apply sum_congr rfl; intro i _; rw [tsum_mul_left]; -- check orientation
           intro j _; exact (((Local.Raw.dominated_pieces 0 hH (hP j).format ((hx' j).income hk le_rfl)).2.summable K).comp_injective Subtype.val_injective).mul_left _
       change hook _ _ U= ∑ i,y i • hook _ _ (V i); rw [hV]
       unfold hook; funext i q; simp only [Finset.sum_apply,Pi.smul_apply, smul_eq_mul,mul_sum]; rw [sum_comm]; refine Finset.sum_congr rfl fun m' _=> ?_; rw [sum_mul]; apply sum_congr rfl; intro j _; ring
    refine ⟨formatPin_sum univ hc, ?_,?_,fun i v₁ v₂ h₁ h₂=>?_⟩
    · change (∑ i,y i • x i).1=A.x; rw [Prod.fst_sum]; change ∑ i,y i • ((P i).seed + ∑' j,g i j)= M.seed+∑' j,M.row 0 S Y R.p.threshold j; simp only [hg,hx, smul_add,sum_add_distrib]; rw [Summable.tsum_finsetSum _ ]; apply congr_arg; apply sum_congr rfl; intro i _; exact ((hy i).tsum_const_smul _).symm; intro i _; exact (hy i).const_smul _
    · funext i; change (∑ i,y i • x i).2.2 i=stowK K A i; rw [Prod.snd_sum, Prod.snd_sum,Finset.sum_apply]; by_cases he:i∈ Set.range (cart K)
      · obtain ⟨k,rfl⟩:=he
        change ∑ i,y i • stowK K (A' i) (cart K _)=_; rw [stowed,hK]; simp_rw [Finset.sum_apply, stowed];rfl
      change ∑ j,y j • stowK K (A' j) i=_; simp_rw [pit _ _ he,smul_zero,sum_const_zero]
    let S':=fun j=>joint B 0 (S j); let O:= tongue S'
    have hp : Sculpts R.p (mapSeat i) (U.2.1 i) (liveE A i):=by
        intro V hz; dsimp only [U]; rw [Prod.snd_sum,Prod.fst_sum,Finset.sum_apply]; change (∑ j,y j • liveE (A' j) i) ∘ increment V=ᶠ[𝓝 0] _
        by_cases hh : i∈Set.range O
        · obtain ⟨j,rfl⟩:= hh
          have h i: liveE (A' i) (O j)= (A' i).regular j:= O.injective.extend_apply ..
          simp_rw [h,show liveE A (O j)=_ from (show liveE A (O j)= A.regular j from O.injective.extend_apply ..)]; apply (hP₀ j V ?_).symm
          rw [show mapSeat (O j)= _ from leased A (usage T hM.format hp hH) j] at hz; exact hz
        simp_rw [show ∀ i',liveE (A' i') i=0 from fun j=> extend_apply' _ _ _ hh,smul_zero,sum_const_zero,show liveE A i=0 from extend_apply' _ _ _ hh]; exact EventuallyEq.rfl
    refine ⟨h₁.1.trans h₂,fun V hV l hl hb=>?_⟩; rw [Local.left_congr l V (hp V hV)]; exact (h₁.2 _ hV _ hl hb).trans h₂
end pack
end YM.MergeProof.Matric
