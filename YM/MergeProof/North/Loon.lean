import YM.MergeProof.North.Blade
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymBooks
import YM.ProjectorNext.EQUATION_CAMPAIGN.Receiving

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Float
open Function Filter Lattice Wilson RG Source Accent Push Local Extra.Histories PhysicalNext.Repeat Lotus Finset Marker Ribbon MeasureTheory
open scoped Topology BigOperators Classical
variable {ι β:Type}{G:Gauge}{n c:Side}{R:Rep G n}{κ e t z a:ℝ} {o:Site n}
section pieces
-- literal membership and mask
variable (F:Config G n→ℂ) {i:Wing} (hr:o∈i.support R) (hb:i.blank R)(h:UsesFinal R.p.threshold (i.support R) F)(hf:GaugeInvariant F)(hx:Measurable F)(he:∀ U,F U≠0→i.qualifies R U) (hp:∀ U, ‖F U‖ ≤ t)
include hb h hf hx he hp
def lilac (g:ℂ→L[ℝ] ℝ)(hg:∀ z,‖g z‖ ≤ ‖z‖) : Leaf R:=⟨i,g ∘ F,fun _ _ he ht=> congr_arg g (h _ _ he ht),fun U hz=>he U (fun h=> hz (by simp [h])),hb,t,fun U=>(hg _).trans (hp _),fun t U=>congr_arg g (hf t U), g.continuous.measurable.comp hx⟩
lemma draws : ∃ M N:Leaf R,M.turn=i ∧ N.turn=i ∧ M.weight=t∧N.weight=t∧F= Complex.ofReal ∘ M.ingredient+Complex.I • (Complex.ofReal ∘ N.ingredient):=by
   refine ⟨lilac F hb h hf hx he hp Complex.reCLM Complex.abs_re_le_norm,lilac F hb h hf hx he hp Complex.imCLM Complex.abs_im_le_norm,rfl,rfl,rfl,rfl,funext fun U=>?_⟩
   let z:= F U; change z= (z.re:ℂ)+Complex.I*(z.im:ℂ); rw [mul_comm Complex.I]; exact z.re_add_im.symm
end pieces
-- vitality if absent separately
lemma petals (A:Menu.Arsenal R)(S:Support n)(f: Config G n→ℂ)(hf:GaugeInvariant f)(hx:Measurable f)(h:UsesFinal R.p.threshold S f)(ht:∀ U,f U≠0→Healthy R.p.threshold S U)(hr:f≠0→ o∈S)(hp:∀ U,‖f U‖≤t): Blade R o f 0 0 (2*R.p.mass S t):=by
   by_cases hh:f=0
   · rw [hh]; exact blade₀ (mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hp 1))))
   obtain ⟨i,hV,hv⟩:= A.dry S ⟨_,hr hh⟩
   let w:= Wing.logKey i; have hg: w.support R=S:=hV
   obtain ⟨M,N,hM,hN,hs,hH,hK⟩:=draws f (show w.blank R from hv) (hg.symm ▸ h) hf hx (fun U hn=> (hV.symm ▸ ht U hn : Healthy R.p.threshold (R.activities.reg i).support U)) hp
   have hx : M.crest=S:=by unfold Leaf.crest; rw [hM,hg]
   have hy : N.crest=S:=by unfold Leaf.crest; rw [hN,hg]
   have hi:= (bristle M (hx.symm ▸ hr hh)).comp ((bristle N (hy.symm ▸ hr hh)).rate Complex.I)
   rw [hK]; rw [show prose M=Complex.ofReal ∘ M.ingredient from funext fun i=> by unfold prose;rw [hM];rfl,show prose N=Complex.ofReal ∘ N.ingredient from funext fun i=> by unfold prose;rw [hN];rfl,show entry M=0 from funext fun i=>funext fun U=>by unfold entry; rw [hM];rfl, show entry N=0 from funext fun i=>funext fun U=>by unfold entry; rw [hN];rfl,load,load,hx,hy,hs,hH] at hi; simp only [smul_zero,zero_add,mul_zero,Complex.norm_I,one_mul] at hi; rw [two_mul]; exact hi
lemma pillars (A:Menu.Arsenal R)(S:Box n)(f: Config G n→ℂ)(hf:GaugeInvariant f)(hx:Measurable f)(h:UsesFinal R.p.threshold S.1 f)(ht:∀ U,f U≠0→ S.1∩flags R.p.threshold U=S.2 ∧ Sure S)(hr:f≠0→ o∈ S.1)(hp:∀ U,‖f U‖≤t): Blade R o 0 (Pi.single S f) 0 (2* R.p.mass S.1 t):=by
   by_cases hh:f=0
   · rw [hh,Pi.single_zero]; exact blade₀ (mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hp 1))))
   obtain ⟨j,hV,hv⟩:= A.wet S (ht _ (Function.ne_iff.mp hh|>.choose_spec)|>.2)
   let w:= Wing.gasKey j; have hg: w.support R=S.1:=congr_arg Prod.fst hV
   obtain ⟨M,N,hM,hN,hs,hH,hK⟩:=draws f (show w.blank R from trivial) (hg.symm ▸ h) hf hx (fun U hn=>hv U (ht U hn|>.1)) hp
   have he : M.crest=S.1:=by unfold Leaf.crest; rw [hM,hg]
   have hy : N.crest=S.1:=by unfold Leaf.crest; rw [hN,hg]
   have H: entry M+Complex.I • entry N=Pi.single S f:=by
     funext i U; simp only [Pi.add_apply,Pi.smul_apply,entry, hM,hN,hV,w]; by_cases hi:i=S
     · rw [hi,Pi.single_eq_same,hK]; simp
     simp [Ne.symm hi,Pi.single_eq_of_ne hi]
   rw [← H,two_mul]; have hi:= (bristle M (he.symm ▸ hr hh)).comp ((bristle N (hy.symm ▸ hr hh)).rate Complex.I)
   have hz : prose M+Complex.I • prose N=0:=by funext i; simp [prose,hM,hN,w]
   rwa [hz,load,load,he,hy,hs,hH,mul_zero,zero_add,Complex.norm_I,one_mul] at hi
end YM.MergeProof.Float
