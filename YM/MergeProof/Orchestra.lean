import YM.MergeProof.Flavor
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{ι:Type*}{d:ℕ}{F:Labels.Frame G d}{o:Site n}{B:SectionData F}
    {R:Rep G n}{P:BudgetPoint}{f:ι→Response G n}{a:ι→ℝ}[Countable ι]
omit [Countable ι] in
def band (f:ι→Response G n) (p:Support n) U:= ∑' i,f i p U
variable (h:∀ i, Attainment P o (f i) (a i))
include h
lemma perform (hp:Summable a): Attainment P o (band f) (∑' i,a i) ∧ ∀ p U, Summable (fun i=> f i p U):=by
   choose v hv hs using fun i=> (h i).toll
   let c (j : ι×Support n):= reservedMass P j.2 (v j.1 j.2); have hc:= budget_prod (f:=c) hv hp
   let m i:=∑' j,v j i; have hm(i): 0≤ m i:=tsum_nonneg (fun j=> (hs j i).1)
   have hy(i): Summable (fun j=> v j i):=(hc.2.1.prod_symm.prod_factor i).of_nonneg_of_le (fun j=> (hs j i).1) (fun j=> le_mul_of_one_le_left (hs j i|>.1) (Real.one_le_exp (mul_nonneg (add_nonneg P.exponent_pos.le zero_le_two) (by positivity))))
   have he(p U): ‖band f p U‖≤ m p:=by
      have hh := (hy p).of_nonneg_of_le (fun j=> norm_nonneg (f j p U)) (fun j=> (hs j p).2 U); exact (norm_tsum_le_tsum_norm hh).trans (hh.tsum_le_tsum (fun i=> (hs i p).2 U) (hy p))
   refine ⟨⟨fun p=>?_,fun p he=> ?_,m,⟨fun p=> mul_nonneg (Real.exp_pos _).le (hm p),?_,?_⟩,fun i=>⟨hm i,he i⟩⟩,fun p U=> (hy p).of_norm_bounded (fun i=> (hs i p).2 U)⟩
   · exact ⟨fun U V hX ht=>tsum_congr (fun i=> (h i |>.shaped p).sites U V hX ht), fun g U=>tsum_congr (fun i=> (h i |>.shaped p).symmetry g U),Measurable.tsum (fun i=> (h i |>.shaped p).borel),fun U hU=> (tsum_congr (fun i=> (h i |>.shaped p).healthy_zero U hU)).trans tsum_zero⟩
   · by_contra hg; apply he; funext U; exact (tsum_congr (fun i=> congr_fun (not_not.mp (mt ((h i).marked p) hg)) U)).trans tsum_zero
   · unfold reservedMass m; simp_rw [← tsum_mul_left]; exact hc.2.1.prod_symm.prod
   unfold reservedMass m; simp_rw [← tsum_mul_left]; exact (hc.2.1.prod_symm.tsum_prod.symm.trans ((Equiv.prodComm ..).tsum_eq c)).trans_le hc.2.2
omit h [Countable ι] in
lemma hook_charge (A:Activities G n)(t:ℝ)(p:Box n)(U:Config G n)(hf:∀ x,Summable (fun i=> f i x U)):
    HasSum (fun i=>hook A t (f i) p U) (hook A t (band f) p U):=by
   unfold hook; exact hasSum_sum fun i _=> (hf i).hasSum.mul_right _
omit h [Countable ι] in
lemma stackFee {t v : ℝ} {f:Response G n}(hp:Attainment P o f t)(ht:t ≤ v): Attainment P o f v:=by obtain ⟨a,h,hb⟩:= hp.toll; exact ⟨hp.shaped,hp.marked,a,⟨h.1,h.2.1,h.2.2.trans ht⟩,hb⟩
omit h [Countable ι] in
lemma stack_of {t:ℝ} {f:Response G n}(hp:Attainment P o f t)(u:ℂ): Attainment P o (u • f) (‖u‖*t):=by
   obtain ⟨v,h,hf⟩:=hp.toll; refine ⟨fun i=>⟨fun U V hv ht=> congr_arg (u*·) ((hp.shaped i).sites _ _ hv ht),fun g U=>congr_arg (u*·) ((hp.shaped i).symmetry g U), (hp.shaped i).borel.const_mul _,fun U h=>by change u * f i U=0; rw [(hp.shaped i).healthy_zero U h,mul_zero]⟩,fun i h=> hp.marked i (fun he=>h (by change u • f i=0; rw [he, smul_zero])),fun i=> ‖u‖ *v i,?_,fun i=>⟨mul_nonneg (norm_nonneg _) (hf i).1,fun U=>by simp only [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left ((hf i).2 _) (norm_nonneg u)⟩⟩
   refine (show (fun i=> reservedMass P i (‖u‖*v i))=fun i=> ‖u‖*reservedMass P i (v i) from funext fun i=>?_).symm ▸ Local.sumBudget_mul_left h (norm_nonneg u)
   unfold reservedMass; ring
omit h [Countable ι] in
lemma hook_scale (A:Activities G n)(t:ℝ)(f:Response G n)(u:ℂ): hook A t (u • f)=u • hook A t f:=by
   funext i U; simp only [hook,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]
omit h [Countable ι] in
lemma profile_scale (A:Activities G n)(f:ℕ→Config G n→ℂ)(u:ℂ): profile A (u • f)= u • profile A f:=by funext i U; simp only [profile,cram,Pi.smul_apply,smul_eq_mul,tsum_mul_left]
omit h [Countable ι] in
lemma profile_shop {f:ι→ ℕ→Config G n→ℂ}(A:Activities G n)(h:Dominated (fun i:ι×ℕ=>f i.1 i.2)) (p:Box n)(U:Config G n):
    HasSum (fun i=> profile A (f i) p U) (profile A (fun j U=> ∑' i,f i j U) p U):=by
   unfold profile cram; let e(i:ι×{i// barcode A i=p}):= f i.1 i.2.val U; have he: Summable e:= (h.summable U).comp_injective (i:=fun i : ι×{i//barcode A i=p}=> (i.1,i.2.val)) (fun i j he=> Prod.ext (Prod.mk.inj he|>.1) (Subtype.ext (Prod.mk.inj he|>.2))) -- maybe and diff
   rw [show ∑' j:{i//barcode A i=p},∑' i,f i j.val U=∑' i,∑' j:{i// barcode A i=p},f i j.val U from he.tsum_comm]; exact he.prod.hasSum
omit h [Countable ι] in
lemma profile_merge (e:ℕ≃ι×ℕ) (f:ι→Coefficient F n) {x:ℝ}(hx:0<x) (h:∀ i,(f i).remBound o R x (a i))(he:Summable a) (p:Box n)(U:Config G n):
    HasSum (fun i=> profile R.activities (f i).forced p U) (profile R.activities (merge e f).forced p U):=
      profile_shop _ (f:=fun i=>(f i).forced) (merge_budget e f hx h he|>.2.2) _ _
end YM.MergeProof
