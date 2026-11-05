import YM.FullVolume.Shroud.Laws
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Shroud
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Source Labels Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Next.Foundations Push Precision WilsonStartup
open UVNext.CouplingReset UVNext.PricedKernels Ovens Ovens.Pipes Progress.DirectedRecipe BudgetPoint Extra.Iteration
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side} {P:BudgetPoint}{D:PathData G}{c:Clip}{σ C Λ b w:ℝ}
open Quake Well
namespace Muslin
variable (R:Rep G n)(t:ℝ)(h:R.Lawful σ C Λ b w){v a b':ℝ}
set_option quotPrecheck false
local notation "S"=>stitch R t
local notation "p"=> R.p
local notation "u"=>R.p.threshold
include h
lemma grave (hp:w ≤ 1)(g:ℝ)(hg:∀ U, ‖leg R U‖≤g)(hh:|t| *g ≤ 1):
    (S).KBound p (w+ Fintype.card (Hearts n)*(p).mass (Finset.univ:Support n) (2*(|t| *g))) :=by
    let v:=2*(|t| *g); have he:0≤v:=mul_nonneg zero_le_two (mul_nonneg (abs_nonneg _) ((norm_nonneg (leg R 1)).trans (hg 1)))
    have ht (x:Hearts n)(U:Config G n): ‖chart R t x U‖≤v:=by
       unfold chart; split; next=>
          have hb: |-t*leg R U|≤ |t| *g:= (abs_mul ..).trans_le (by rw [abs_neg]; apply mul_le_mul_of_nonneg_left (hg U) (abs_nonneg _))
          rw [song,Real.norm_eq_abs,abs_mul]; exact ((mul_le_mul (Real.abs_exp_sub_one_le (hb.trans hh)) (SectorNext.Vacuum.gas_le_one _ hp h.labels U) (abs_nonneg _) (mul_nonneg zero_le_two (abs_nonneg _))).trans ((mul_one _).le)).trans (mul_le_mul_of_nonneg_left hb zero_le_two)
       rw [norm_zero]; exact he
    obtain ⟨a,ha,hq⟩:= h.labels.boundK; let K:=guardK (n:=n); let f:= Sum.elim a (fun _:Hearts n=> v) ∘ K
    have hg(i):f (K.symm i)= Sum.elim a (fun _:Hearts n=>v) i:=by simp only [f,Function.comp_apply,Equiv.apply_symm_apply]
    refine ⟨f,fun i=>?_,fun x=>?_⟩
    · obtain ⟨i,rfl⟩:= K.symm.surjective i; rw [hg,show (S).K (K.symm i)=_ from ks' R t i]; cases i; exact ha _; exact ⟨he,ht _⟩
    let g i:= if x∈ ((S).forced i).support then R.p.mass ((S).forced i).support (f i) else 0
    apply transfer_budget K.symm.toEmbedding (f:=g) (g:=fun i=>g (K.symm i)) (fun i=>rfl) (fun i hi=> False.elim (hi (K.symm.surjective i)))
    apply Cost.sum (show SumBudget (fun i=>g (K.symm (.inl i))) w from (by unfold g; simp_rw [hg]; unfold K; simp_rw [ks,Sum.elim_inl]; exact hq x))
    change SumBudget (fun i=> g (K.symm (Sum.inr i))) _; unfold g; simp_rw [hg]; unfold K; simp_rw [ks,Sum.elim_inr,dyed]; simp_rw [Finset.mem_univ, if_true]; refine ⟨fun i=> mul_nonneg (Real.exp_pos _).le he,Summable.of_finite,?_⟩; rw [tsum_fintype]; simp [v]
-- exp harvest
variable (hp : Decent R.clip R.p) (hw:Geo.Width R.p R.clip σ)
def adorn (R:Rep G n)(t:ℝ) : Rep G n:={R with beta:=R.beta-t, activities:= stitch R t}
include hp hw
lemma honors (hv:(stitch R t).Valid R.p a b'): (adorn R t).eval=R.eval:=by
    let D:= adorn R t; ext U; let V:=flags u U=∅; let f(U:Config G n):= BetaTransport.kinetic R.path R.clip p U
    have hp' : (S).additive R.p U= R.activities.additive p U+if flags R.p.threshold U=∅ then t*f U else 0:=by
       let k:=mood (n:=n); let v i:= (S).regularOccurrence R.p (k.symm i) U; have hz:Summable v:=(Activities.ESeries hv|>.summable U).comp_injective k.symm.injective
       have he i:v (.inl i) = _:= show v (.inl i)=R.activities.regularOccurrence R.p i U from by unfold v k Activities.regularOccurrence; rw [es,es'];rfl
       have hh i:v (.inr i)=RG.masked u (herb i|>.support) (grain R.path R.clip t i) U:=by unfold v k Activities.regularOccurrence; rw [es,es']; rfl
       rw [Activities.additive,← k.symm.tsum_eq (fun i=>(S).regularOccurrence R.p i U)]
       change (∑' i,v i)= _; rw [(hz.comp_injective Sum.inl_injective).tsum_sum (hz.comp_injective Sum.inr_injective)]; simp_rw [he,hh]; rw [withherb R.path R.clip h.paths hp hw]; rfl
    rw [Rep.eval, Rep.eval]; unfold adorn; dsimp only [Rep.exponent]; rw [hp', exposed R t h hv U]; let s:= R.beta
    rw [BetaTransport.channels_split _ (R.beta-t)]
    have hg:= BetaTransport.channels_split (D:=R.path) («P»:=R.p) (A:=R.clip) U R.beta
    split_ifs
    · rw [hg]; dsimp only [f]; congr 2; ring
    rw [← mul_assoc,← Real.exp_add,hg]; congr 2; ring
omit h hp hw
lemma earned (P:BudgetPoint)(c:Clip)(σ C Λ g e w w':ℝ)(hg:g<e)(hw:w<w')(hy:w≤1)(hp:4≤ n.val)(hd:Decent c P)(hv:Geo.Width P c σ): ∃ t:ℝ, 0<t∧∀ a:ℝ, |a| ≤t → ∀ R:Rep G n, R.p=P→ R.clip=c → R.Lawful σ C Λ g w → (adorn R a).Lawful σ C Λ e w' ∧ (adorn R a).eval=R.eval:=by
    obtain ⟨u',hx,hB⟩:= gasoline P c σ C Λ n (G:=G); let b:= fun t:ℝ=> costs G n P t c σ C; let f t:= (Fintype.card (Hearts n):ℝ)* P.mass (Finset.univ:Support n) (2*(|t| *u'))
    have hm:Tendsto b (𝓝 0) (𝓝 0):=(show Continuous b from by unfold b costs; fun_prop).tendsto' _ _ (by simp [b,costs])
    -- edit
    have hz : Tendsto f (𝓝 0) (𝓝 0):= (show Continuous f from by unfold f BudgetPoint.mass; fun_prop).tendsto' _ _ (by simp [f,BudgetPoint.mass])
    have hA : Tendsto (fun t:ℝ=>|t| *u') (𝓝 0) (𝓝 0):= (show Continuous (fun t:ℝ=> |t| *u') from by fun_prop).tendsto' _ _ (by simp)
    obtain ⟨t,ht,hH⟩:= Metric.nhds_basis_closedBall.mem_iff.mp ((hm.eventually (ge_mem_nhds (sub_pos.mpr hg))).and ((hz.eventually (ge_mem_nhds (sub_pos.mpr hw))).and (hA.eventually (ge_mem_nhds zero_lt_one))))
    refine ⟨t,ht,fun x hε R hP he h=>?_⟩; obtain ⟨hX,hf,hK⟩:= hH (show x∈ Metric.closedBall (0:ℝ) t from by simpa [Metric.mem_closedBall,Real.dist_eq] using hε); have hv: Geo.Width R.p R.clip σ:=by rw [hP,he];exact hv
    have hd: Decent R.clip R.p:=by rw [hP,he];exact hd
    have hi : (stitch R x).Valid R.p e w':=by
       have hb(U:Config G n): ‖leg R U‖≤ u':=by unfold Well.leg; rw [hP,he]; apply hB; exact he ▸ h.paths
       refine ⟨estate R x h hd hp,strands R x h,fun t x'=> involves R x t x' (h.labels.moves t x').some,Time.E_rises (budgets R x h hd) ?_,Time.K_rises (grave R x h hy _ hb hK) ?_⟩
       · rw [hP,he]; change b x≤ e-g at hX; unfold b at hX; linarith only [hX]
       rw [hP]; change _ + f x≤_; change f x ≤ w'-w at hf; linarith only [hf]
    exact ⟨⟨h.paths,hi⟩, honors R x h hd hv hi⟩
end Muslin
end YM.FullVolume.Shroud
#print axioms YM.FullVolume.Shroud.Muslin.earned
