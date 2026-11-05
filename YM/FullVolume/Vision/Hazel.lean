import YM.FullVolume.Vision.Score
/-! Flow convergence to implicit branch.Via arrow composition at EVERY finite order. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Change.Reading
open Function Filter Precision Work
open scoped Topology ContDiff BigOperators Classical
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]{n:ℕ}
variable {v:ℕ→ X→ Y}{w:X→Y}{S:ℕ→ Y→ Z}{s:Y→ Z}{x:X}
private noncomputable def bevel (f : X→Y) (g:Y→Z) (x:X)(n:ℕ):= (ContinuousLinearMap.inverse (fderiv ℝ g (f x))).compContinuousMultilinearMap (sign (g∘ f) x n-carta g f n x (f x))
private lemma bearing (hn:0<n)(h:ContDiffAt ℝ ω w x)(he:ContDiffAt ℝ ω s (w x))(hy:(fderiv ℝ s (w x)).IsInvertible): bevel w s x n= sign w x n:=by
     unfold bevel; rw [docking he h hn,add_sub_cancel_right]; obtain ⟨e,h⟩ :=hy; rw [← h]; ext1 v; change ContinuousLinearMap.inverse _ (e (sign w x n v))=_; simp
lemma View.exposes (h:View S s (fun i=> v i x) (w x))(hp: ∀ᶠ i in atTop,ContDiffAt ℝ ω (v i) x)(hx:ContDiffAt ℝ ω w x)(hz:Tendsto (fun i=>v i x) atTop (𝓝 (w x)))(H:View (fun i=> S i∘ v i) (s∘w) (fun _=>x) x)(hf:∀ᶠ i in atTop,(fderiv ℝ (S i) (v i x)).IsInvertible)(he:(fderiv ℝ s (w x)).IsInvertible) [CompleteSpace Y] : View v w (fun _=>x) x:=by
    refine ⟨hp,hx,fun i=>?_⟩
    induction i using Nat.strong_induction_on with
    | h i ih=>
     by_cases hh : i=0
     · subst i; simp_rw [iteratedFDeriv_zero_eq_comp, comp_apply]; exact (continuousMultilinearCurryFin0 ℝ X Y).symm.continuousAt.tendsto.comp hz
     have hw := H.goals i; have hk:= h.further.value; let p:ℕ→X:=fun _=>x; have hV:= View.rest (r:=x) (x:=p) (F:=w) (f:=v) h ih
     have hI:= he.contDiffAt_map_inverse (n:=ω)|>.continuousAt|>.tendsto|>.comp hk
     let T(r : Z→L[ℝ] Y): Tensor.T X Z i →L[ℝ] Tensor.T X Y i:= ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ Z Y r
     have hl: Continuous fun p:(Z→L[ℝ] Y) × Tensor.T X Z i => T p.1 p.2 := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ Z Y).continuous.comp continuous_fst).clm_apply continuous_snd
     have hY:Tendsto (fun j=> bevel (v j) (S j) x i) atTop (𝓝 (bevel w s x i)):= hl.continuousAt.tendsto.comp (hI.prodMk_nhds (hw.sub hV))
     have hB : 0 < i:=Nat.pos_of_ne_zero hh; rw [bearing hB hx h.star he] at hY
     exact hY.congr' ((hp.and (h.against.and hf)).mono fun i ht=> bearing hB ht.1 ht.2.1 ht.2.2)
variable {f:ℕ→X×Y→ℝ}{F:X×Y→ℝ}{u:ℕ→X→Y}{r:X→Y}
private lemma tilted [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y](h: Definite F) (hv:Station F r) : (fderiv ℝ (arrow F) (graph r 0)).IsInvertible:=by
     rw [hv.at0]; obtain ⟨U,hU⟩ := h.equiv; exact ⟨U,hU.fderiv.symm⟩
lemma View.forecast {f:ℕ→X×Y→Z}{F:X×Y→Z}(h:View f F 0 0): View (fun i=>vert (f i)) (vert F) 0 0:=by
    let L(s:(X×Y→L[ℝ]Z)):=s.comp (ContinuousLinearMap.inr ℝ X Y)
    have hd:ContDiff ℝ ω L:=contDiff_id.clm_comp contDiff_const
    have H(f:X×Y→Z)(h:ContDiffAt ℝ ω f 0): L ∘ fderiv ℝ f =ᶠ[𝓝 0] vert f:=by
        filter_upwards [h.eventually (by simp)] with ⟨x,y⟩ hp
        have ht : HasFDerivAt (fun y : Y => (x,y)) (ContinuousLinearMap.inr ℝ X Y) y := (hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)
        exact ((hp.differentiableAt (by simp)).hasFDerivAt.comp y ht).fderiv.symm
    exact (h.further.compose hd.contDiffAt).ferry (H _ h.star) (h.against.mono fun i hi=> H _ hi)
lemma stability [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y](h: View f F 0 0)(hs:Definite F)(hp:Station F r)(he:∀ᶠ i in atTop, Definite (f i) ∧ Station (f i) (u i)): View (fun i=> graph (u i)) (graph r) 0 0 :=by
    haveI := FiniteDimensional.complete ℝ X; haveI := FiniteDimensional.complete ℝ Y
    have h': View (fun i=> arrow (f i)) (arrow F) 0 0:= (View.checked contDiffAt_fst (x:=fun _:ℕ=>(0:X×Y)) tendsto_const_nhds).twins h.forecast
    have hZ : View (fun i=> arrow (f i)) (arrow F) (fun i=> graph (u i) 0) (graph r 0) := (hp.at0).symm ▸ (h'.points (he.mono fun i hi=>hi.2.at0.symm))
    have hM : (fun i=> graph (u i) 0)=ᶠ[atTop] (fun _=> graph r 0) := he.mono fun i hi=> hi.2.at0.trans hp.at0.symm
    let g(x:X): X× (Y→L[ℝ]ℝ):=(x,0)
    have hG : ContDiff ℝ ω g:= contDiff_id.prodMk contDiff_const
    exact hZ.exposes (he.mono fun i hi=> hi.2.chart) hp.chart (tendsto_const_nhds.congr' hM.symm) ((View.checked (x:=fun _=>0) hG.contDiffAt tendsto_const_nhds).ferry (portico hp).symm (he.mono fun i hi=> (portico hi.2).symm)) (he.mono fun i hi=> tilted hi.1 hi.2) (tilted hs hp)
end YM.WilsonStartup.Change.Reading
