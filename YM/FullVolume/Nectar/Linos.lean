import YM.FullVolume.Nectar.Avalon
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
open Function Filter Set MeasureTheory Finset FullVolume.Ray
open scoped Topology BigOperators Classical ContDiff
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]{b c v:ℝ}
variable {w:Rung}
def dose (w:Rung) (f:sun→ℝ):Rung:=∑ i∈w.support,Finsupp.single i (w i * f i)
lemma drumMix (f:sun→ℝ) (g:sun→E)(w:Rung):mix w (fun t=>f t • g t)=mix (dose w f) g:=by
   rw [← combo_eq (dose ..)]; unfold dose; rw [map_sum]; unfold mix; apply Finset.sum_congr rfl; intro i _; rw [smul_smul, combo,Finsupp.linearCombination_single] -- _
lemma titrate {F:sun→ℝ}(h:Scout b (phraseS F) c)(hv:Stripe w b v): Stripe (dose w F) b (v*c):=by
   have ht:= h.ray;have hβ : b>0:= zero_lt_one.trans_le ht
   intro i
   let p(t:ℝ):= (t/b)^i; rw [← mix_id,←drumMix];
   have hp:Scout b p 1:=by
       have hh:= (Scout.line ht|>.scale b⁻¹); rw [norm_inv,Real.norm_of_nonneg hβ.le,inv_mul_cancel₀ hβ.ne'] at hh
       have ht:= hh.power i; rw [one_pow] at ht; exact ht.replace (fun t _=>by unfold p; change (b⁻¹*t)^i=_;rw [mul_comm (b⁻¹) t,div_eq_mul_inv])
   have hg:=h.multiplies hp; rw [mul_one] at hg
   have h': Scout b (phraseS (fun t:sun=> F t*(t.val/b)^i)) c:= hg.replace (fun x hx=>by
       let t:sun:=⟨x,hx⟩; change phraseS F x*p x=_; rw [show phraseS F x=F t from phrased _ t]; change F t * p x= _; rw [show phraseS _ x= _ from phrased (fun t:sun=> F t*(t.val/b)^i) t])
   exact mix_d _ hv h'
lemma rebarMul {A:sun→E}{f:sun→ℝ}(h: Rebar b (phraseS A) v)(hz:Scout b (phraseS f) c): Rebar b (phraseS (fun t=> f t • A t)) (c*v):=⟨h.ray,mul_nonneg hz.nonneg h.nonneg,fun w η ht=>by
    have h':= h.beam _ _ (titrate hz ht); rw [mix_made,drumMix]; rw [mix_made] at h'; exact h'.trans_eq (mul_assoc ..)⟩
lemma rebarSum {ι:Type*}(u:Finset ι) (f:ι→sun→E)(r:ι→ℝ)(h:∀ i∈u,Rebar b (phraseS (f i)) (r i))(hp:1≤b): Rebar b (phraseS (fun x=>∑ i∈u,f i x)) (∑ i∈u,r i):=by
   refine ⟨hp,sum_nonneg (fun _ hi=>(h _ hi).nonneg),fun w η ht=>?_⟩
   have hA: trace w (phraseS (fun x=>∑ i∈u,f i x))=∑ i∈u,trace w (phraseS (f i)):=by unfold trace phraseS; simp_rw [smul_sum]; exact Finset.sum_comm
   rw [hA, Finset.mul_sum]; exact (norm_sum_le ..).trans (sum_le_sum fun i hi=> (h i hi).beam _ _ ht)
open FullVolume.Ray.Nail
abbrev billboardC (k:ℕ) (p:ℝ) := (FullVolume.Ray.bounty (sampleP k) *p^k) -- ensure imports
lemma survey {k:ℕ}{f:sun→ E}{g:Fin (k+1) → sun → E}(h:∀ i,Rebar b (phraseS (g i)) c)(hv:1≤b)
    (ht:∀ s:sun,f s=∑ i,Nail.title k i s • g i s): Rebar b (phraseS f) (billboardC k b*c):=by
      let u(i):=(FullVolume.Ray.pot (sampleP k) i)*b^k; let F(i)(s:sun):=Nail.title k i s • g i s
      have hh i:Scout b (phraseS (Nail.title k i)) (u i):=(candles (sampleP k) (Subtype.val_injective.comp (samples_in k)) hv i).replace fun s hs=> (phrased (Nail.title k i) ⟨s,hs⟩).symm
      rw [show billboardC k b*c=∑ i,u i*c from (by unfold billboardC FullVolume.Ray.bounty; rw [sum_mul,sum_mul]), show f=(fun s=>∑ i,F i s) from funext ht]; exact rebarSum univ F _ (fun i _=> rebarMul (h i) (hh i)) hv
end YM.PhysicalNext.Repeat.Jams
