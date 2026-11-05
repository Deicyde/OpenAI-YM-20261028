import YM.FullVolume.Vision.Epine
/-! ALL levels germ convergence with composition.Pictures... -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Change.Reading
open Function Filter Precision Work OrderedFinpartition
open scoped Topology ContDiff BigOperators Classical
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]{n:ℕ}
variable {f g : ℕ→ X → Y}{F G:X→Y}{x:ℕ→X}{r:X}
structure View (f:ℕ→ X→Y)(F:X→Y)(x:ℕ→X)(r:X): Prop where
   against : ∀ᶠ i in atTop,ContDiffAt ℝ ω (f i) (x i)
   star : ContDiffAt ℝ ω F r
   goals j : Tendsto (fun i=> iteratedFDeriv ℝ j (f i) (x i)) atTop (𝓝 (iteratedFDeriv ℝ j F r))
namespace View
variable {v:View f F x r}
lemma value (v:View f F x r): Tendsto (fun i=> f i (x i)) atTop (𝓝 (F r)):=by
    have H:= (ContinuousMultilinearMap.apply ℝ _ Y (0:Fin 0→X)).continuous.continuousAt.tendsto.comp (v.goals 0); simpa [Function.comp_def] using H
lemma points (h:View f F x r){y} (he:x=ᶠ[atTop] y): View f F y r:=⟨ (h.against.and he).mono fun i hi=> hi.2 ▸ hi.1,h.star,fun j=>(h.goals j).congr' (he.mono fun i hi=> congr_arg _ hi)⟩
lemma ferry (h:View f F x r)(he: F=ᶠ[𝓝 r] G)(hp:∀ᶠ i in atTop,f i=ᶠ[𝓝 (x i)] g i): View g G x r:=
    ⟨(h.against.and hp).mono fun i hi=>hi.1.congr_of_eventuallyEq hi.2.symm,h.star.congr_of_eventuallyEq he.symm,fun j=> by rw [← (he.iteratedFDeriv ℝ j).self_of_nhds]; exact (h.goals j).congr' (hp.mono fun i hi=> (hi.iteratedFDeriv ℝ j).self_of_nhds)⟩
lemma checked (hf:ContDiffAt ℝ ω F r)(he:Tendsto x atTop (𝓝 r)): View (fun _=> F) F x r:=⟨he.eventually (hf.eventually (by simp)),hf,fun j=>(hf.continuousAt_iteratedFDeriv le_top).tendsto.comp he⟩
lemma plus (hf:View f F x r)(hg:View g G x r): View (fun i=> f i+g i) (F+G) x r:=by
   refine ⟨(hf.against.and hg.against).mono fun i h=> h.1.add h.2,hf.star.add hg.star,fun j=>?_⟩
   rw [iteratedFDeriv_add_apply (hf.star.of_le le_top) (hg.star.of_le le_top)]; exact ((hf.goals j).add (hg.goals j)).congr' ((hf.against.and hg.against).mono fun i h=> (iteratedFDeriv_add_apply (h.1.of_le le_top) (h.2.of_le le_top)).symm)
lemma tune (hf:View f F x r)(hg:View g G x r): View (fun i=> f i - g i) (F-G) x r:=by
   refine ⟨(hf.against.and hg.against).mono fun i h=> h.1.sub h.2,hf.star.sub hg.star,fun j=>?_⟩
   rw [iteratedFDeriv_sub_apply (hf.star.of_le le_top) (hg.star.of_le le_top)]; exact ((hf.goals j).sub (hg.goals j)).congr' ((hf.against.and hg.against).mono fun i h=> (iteratedFDeriv_sub_apply (h.1.of_le le_top) (h.2.of_le le_top)).symm)
lemma coin (h: View f F x r)(c:ℝ): View (fun i=> c • f i) (c • F) x r:=by
   refine ⟨h.against.mono fun i H=> H.const_smul c,h.star.const_smul c,fun j=>?_⟩
   rw [iteratedFDeriv_const_smul_apply (h.star.of_le le_top)]; exact ((h.goals j).const_smul c).congr' (h.against.mono fun i hi=> (iteratedFDeriv_const_smul_apply (hi.of_le le_top)).symm)
lemma further (hf:View f F x r): View (fun i=> fderiv ℝ (f i)) (fderiv ℝ F) x r:=by
   refine ⟨hf.against.mono fun i H=>H.fderiv_right le_top,hf.star.fderiv_right le_top,fun i=>?_⟩
   let L:=continuousMultilinearCurryRightEquiv' ℝ i X Y
   have ht (f:X→Y)(p:X): L (iteratedFDeriv ℝ (i+1) f p)=iteratedFDeriv ℝ i (fderiv ℝ f) p:=by rw [iteratedFDeriv_succ_eq_comp_right]; exact L.apply_symm_apply _
   simp_rw [← ht]; exact L.continuousAt.tendsto.comp (hf.goals _)
-- CMM comp weighting
variable {h:ℕ→Y→Z}{H:Y→Z}
private lemma merge (c:OrderedFinpartition n) {P:ℕ→Tensor.T Y Z c.length}{V}{R:ℕ→∀ i, Tensor.T X Y (c.partSize i)}{W} (h:Tendsto P atTop (𝓝 V))(g:∀ j,Tendsto (fun i=> R i j) atTop (𝓝 (W j))):Tendsto (fun i=>(c.compAlongOrderedFinpartitionL ℝ X Y Z (P i)) (R i)) atTop (𝓝 (c.compAlongOrderedFinpartitionL ℝ X Y Z V W)):=by
   exact (c.compAlongOrderedFinpartitionL ℝ X Y Z).continuous_uncurry_of_multilinear.continuousAt.tendsto.comp (h.prodMk_nhds (tendsto_pi_nhds.mpr g))
lemma comp (hf:View f F x r)(hp:View h H (fun i=> f i (x i)) (F r)):View (fun i=> h i∘ f i) (H∘F) x r:=by
    refine ⟨(hf.against.and hp.against).mono (fun i ht=> ht.2.comp (x i) ht.1),hp.star.comp r hf.star,fun j=> ?_⟩
    have ht (p:OrderedFinpartition j):= merge (X:=X) p (hp.goals p.length) fun i=> hf.goals (p.partSize i)
    rw [iteratedFDeriv_comp hp.star hf.star le_top]
    exact (tendsto_finsetSum Finset.univ fun i _=> ht i).congr' ((hf.against.and hp.against).mono fun i ht=> (iteratedFDeriv_comp ht.2 ht.1 (i:=j) le_top).symm)
lemma compose (hf:View f F x r)(hb:ContDiffAt ℝ ω H (F r)): View (fun i=> H ∘ (f i)) (H∘F) x r:= hf.comp (checked hb hf.value)
lemma rest (hp:View h H (fun i=>f i (x i)) (F r))(hx:∀ m,m<n→ Tendsto (fun i=>sign (f i) (x i) m) atTop (𝓝 (sign F r m))): Tendsto (fun i=> carta (h i) (f i) n (x i) (f i (x i))) atTop (𝓝 (carta H F n r (F r))):=by
    unfold carta; exact tendsto_finsetSum _ fun i hi=> merge i (hp.goals _) (fun j=> hx (i.partSize j) (part_small i (Finset.mem_filter.mp hi).2 j))
lemma twins {g:ℕ→ X→Z}{G:X→ Z}(h:View f F x r)(hb:View g G x r): View (fun i x=>(f i x,g i x)) (fun x=>(F x,G x)) x r :=by
   -- avoid prod operations via CLM
   have H:= h.compose (H:=ContinuousLinearMap.inl ℝ Y Z) (ContinuousLinearMap.inl ℝ Y Z |>.contDiff.contDiffAt)
   have H':= hb.compose (H:=ContinuousLinearMap.inr ℝ Y Z) (ContinuousLinearMap.inr ℝ Y Z |>.contDiff.contDiffAt)
   refine (H.plus H').ferry (Eventually.of_forall fun x=> ?_) (Eventually.of_forall fun i=>Eventually.of_forall fun x=>?_)
   all_goals first|exact (Prod.mk_add_mk ..).trans (by simp)| simp
end View
end YM.WilsonStartup.Change.Reading
