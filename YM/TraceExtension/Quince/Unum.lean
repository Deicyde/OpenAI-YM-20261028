import YM.TraceExtension.Quince.Lilt
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG Wilson Finset Source Extra.Histories Labels
open Push Local Next.Foundations Cub
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{R:Rep G n}{o:Site n}{H:Hol G}{d:ℕ}{F:Frame G d}{Y:SectionData F}{x:F.Coeff}
variable {P Q: Coefficient F n}{v a b w : ℝ}
def fineK (F:Frame G d):= Local.testPrice F * ((∑ i∈tests F, partPrice H i)*Cub.gaugeMeter d)
lemma unique_part (hR:Local.Readable H Y R.p n w)(he:P.Format 0 H R)(hf:Q.Format 0 H R)(hp:P.remBound 0 R v a)(hk:Q.remBound 0 R v b)(hV:P.density 0 Y R=Q.density 0 Y R) (m:ℕ)(hm: 10*(m*(4*R.p.B+2)+2*R.p.B)< n.val):
    F.coeffSize (P.x-Q.x) ≤ fineK (H:=H) F * (Real.exp (-R.p.supportExponent*m)*(a+b)):=by
    obtain ⟨t,s,h0,h1,hx,hv,⟨p,hP,hA⟩,-⟩:= hp
    obtain ⟨u,l,h2,h3,hy,hV₀,⟨q,hQ,hB⟩,-⟩:= hk
    let f: ℕ⊕ℕ → Config G n→ℂ :=Sum.elim (fun i=>Q.regular i) (fun i=>(-1:ℂ) • P.regular i)
    let C:ℕ⊕ℕ→Support n:=Sum.elim Q.support P.support; let W:ℕ⊕ℕ→ℝ:=Sum.elim q p
    have G'(i:ℕ⊕ℕ): (R.p).Regular (C i) (f i):= by cases i; exact hf.smooth _; exact Next.Foundations.regular_smul _ (he.smooth _)
    have H'(i:ℕ⊕ℕ): R.p.supBounds (0:Site n) (C i) (f i) (W i):=by cases i with
       | inl i=>exact hB i
       | inr i=> have hp:= Next.Foundations.bound_smul (-1:ℂ) (hA i); rw [norm_neg,norm_one,one_mul] at hp; exact hp
    have hF:SumBudget (fun i:ℕ⊕ℕ=> R.p.mass (C i) (W i)) (a+b):=by
       have Hq := hQ.2.1.hasSum; have Hp:= hP.2.1.hasSum
       let g(i:ℕ⊕ℕ):= R.p.mass (C i) (W i)
       have hi: HasSum g _ := HasSum.sum (show HasSum (g ∘ Sum.inl) _ from Hq) Hp
       refine ⟨fun i=> (H' i).1.trans (R.p.loMass _ _ (H' i).1),hi.summable,le_trans hi.tsum_eq.le ?_⟩; linarith [hP.2.2,hQ.2.2]
    have H₁(i:ℕ⊕ℕ): (0:Site n)∈ C i :=by cases i; exact hf.origin _; exact he.origin _
    have H₂(i:ℕ⊕ℕ) : Nonwrapping (C i) 0→ H.PiVanish d (0: Site n) (f i):=by cases i; exact hf.projects _;exact (stretch_format (-1:ℂ) he).projects _
    let g:=Local.presented Y (0:Site n) R.p.threshold (P.x-Q.x); have hy(U:Config G n)(hp:U∈dent R.p) : g U=∑' i,f i U:=by
       have hs:=line_caps (f:=f) H' (show Summable W from Summable.of_nonneg_of_le (fun i=> (H' i).1) (fun i=> R.p.loMass _ _ (H' i).1) hF.2.1) U hp [] (by simp) (by simp)
       let F(i:ℕ⊕ℕ):= f i U; change Summable (fun i=>‖F i‖) at hs; have hs':=hs.of_norm
       have hu: Summable (fun i=>P.regular i U):=by
            have hF:(F ∘ Sum.inr)=fun i=>-P.regular i U:=by simp [F,f,comp_def];
            have ht:= hs.of_norm; exact summable_neg_iff.mp (show Summable _ from hF ▸ ht.comp_injective Sum.inr_injective)
       have hx:= congr_fun hV U; rw [wiping hR.sound _ he _ hp,wiping hR.sound _ hf _ hp] at hx
       have hx : wipe Y P R U=wipe Y Q R U:=mul_left_cancel₀ (by exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hx
       unfold g; rw [map_sub]; unfold wipe at hx; rw [← show (∑' i,Q.regular i U)-(∑' i,P.regular i U)=(∑' i,f i U) from ?_]; swap
       · have hh:= (hs'.comp_injective Sum.inl_injective).hasSum; rw[sub_eq_add_neg]; apply Eq.symm; refine (?_ : HasSum F _).tsum_eq; exact HasSum.sum hh (Eq.mpr (by simp [Function.comp_def,f,F]) (hu.hasSum.neg))
       rw [Pi.sub_apply]; linear_combination (norm:=ring_nf) hx
    let V:= fun q:Probe G d=> partPrice H q; let z:=∑ i∈tests F,V i; let Z:=Real.exp (-R.p.supportExponent*m)*(a+b); have hd:0≤Z:=mul_nonneg (Real.exp_pos _).le ((tsum_nonneg hF.1).trans hF.2.2)
    have he : fineK (H:=H) F * Z=Local.testPrice F * (z * (Cub.gaugeMeter d *Z)):=by unfold fineK; change Local.testPrice F * (z * Cub.gaugeMeter d) * Z=_; ring
    rw [he]; have hp := zero_le_one.trans (Cub.horizon (d:=d)); apply (Local.probe_budget F).choose_spec.choose_spec.2 _ _ (mul_nonneg (Finset.sum_nonneg (fun i _=> zero_le_one.trans (partPrice_pos H i))) (mul_nonneg hp hd))
    intro p hP; apply (loom_s G' H' hF H₁ H₂ hm hy hR p).trans; exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=V) (fun i _=>zero_le_one.trans (partPrice_pos H i)) hP) (mul_nonneg hp hd)
end YM.PhysicalNext.Repeat.Quince
