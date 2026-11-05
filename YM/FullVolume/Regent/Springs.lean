import YM.FullVolume.Regent.Receives
/-! On true curves.Static period.Limit.Life Vertex Dthermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Beacon
open Lattice RG Precision Wilson Filter Function Laurent Bloch Exterior Next.Free.Retort Tralis Shade Flagship
open WilsonStartup.Change WilsonStartup.Change.Reading
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n m:Side}{p:Clip}{R:ℕ→ PathData G}{P:PathData G}{w a c:ℝ}{S:StepData n m}{V:Reel G}{F: Tree.Forest S.ratio}
private lemma main_germ {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X](U:X→Config G m){x:X→ Link G m}(h: input G m ∘ x=ᶠ[𝓝 0] U): intended p P ∘ x =ᶠ[𝓝 0] mainTerm p P ∘ U:= h.fun_comp _
variable {r:ℕ→ Bid.Dir G n→ AxisChart G F}{η:ℝ} (h:Calm V R P p w a c) (he:∀ᶠ i in atTop, Critical F p (R i) (r i) ∧ PriceGap F p (R i) η)
include h he
lemma Calm.pullback (t:S.Choices) : View (fun i=>onSlice F t p (R i)) (onSlice F t p P) 0 0:=by
   let U:=fun x:VChart G F=>readFine F x
   obtain ⟨x,hX,hT,hV⟩:=reverse_run U (readFine_one _) (readFine_diff _)
   have hu : View (fun i=>mainTerm p (R i) ∘ U) (mainTerm p P ∘ U) 0 0:=by
       refine ((View.checked (x:=fun _=>0) hT tendsto_const_nhds).comp ?_).ferry (main_germ U hV) (Eventually.of_forall fun _=>main_germ U hV); rw [hX]; exact h.harvest.1
   let f := fun z:VChart G F=> noiseTaylor S (represent z.1) (U z) t
   have hp : ContDiffAt ℝ ω f 0:=by
       obtain ⟨i,hi,hj⟩:= (hu.against.and he).exists
       rw [show f= uncurry (tested F t p (R i))-mainTerm p (R i)∘U from funext fun i=>(add_sub_cancel_left ..).symm]; exact (hj.1.2.2 t).1.sub hi
   exact hu.plus (View.checked (x:=fun _=>0) hp tendsto_const_nhds)
lemma hatch : PriceGap F p P η:=by
   intro t v
   let X:=ContinuousLinearMap.inr ℝ (fieldDir G n 1) (AxisChart G F)
   have hV := h.pullback he t; have hp:View (fun i=>tested F t p (R i) 0) (tested F t p P 0) 0 0:=by
       refine (View.checked (F:=fun y=>X y) (x:=fun _=>0) X.contDiff.contDiffAt tendsto_const_nhds).comp (h:=fun i=>onSlice F t p (R i)) (H:=onSlice F t p P) ?_
       simp_rw [map_zero]; exact hV
   exact ge_of_tendsto ((ContinuousMultilinearMap.apply ℝ _ ℝ ![v,v]).continuous.continuousAt.tendsto.comp (hp.goals 2)) (he.mono fun i hi=> hi.2 t v)
lemma pollination (hp:0<η)(hs:S.patch.Branches S.kernel G): ∃ u:Bid.Dir G n→AxisChart G F,Critical F p P u:=by
   refine new_crit hs (fun i=>(h.pullback he i).star) (hatch h he) hp fun j=> ?_
   refine tendsto_nhds_unique (View.value (View.forecast (h.pullback he j))) ?_
   refine tendsto_const_nhds.congr' (he.mono fun i hi=>?_) ; have hb : (r i) 0=0:=hi.1.1
   have hv:= (station_of hi.1 j); have hx := hv.law.self_of_nhds; unfold Function.comp at hx; rw [hv.at0] at hx; exact hx.symm
variable {u:Bid.Dir G n→AxisChart G F}(hp:Critical F p P u)
include hp
lemma dreams (hw:0<η): View r u 0 0:=by
    let t := Classical.arbitrary S.Choices; have hx:= h.pullback he t
    have hg := station_of hp t; have ht := stability hx (definite_of (hatch h he) hw t hx.star) hg (he.mono fun i hi=>⟨definite_of hi.2 hw t (hi.1.2.2 t).1,station_of hi.1 t⟩)
    exact ht.compose (H:=Prod.snd) contDiffAt_snd
private lemma mirrorB (t:S.Choices): View (fun i x=> (hessian F t p (R i) x.1 x.2).det) (fun x : VChart G F => (hessian F t p P x.1 x.2).det) 0 0:=by
    let E:= Precision.Key F G; let X:= h.pullback he t; let f(D:PathData G) (x:VChart G F):= WilsonStartup.Change.vert (WilsonStartup.Change.vert (onSlice F t p D)) x
    let L(D:AxisChart G F→L[ℝ] AxisChart G F→L[ℝ]ℝ):= Matrix.of fun (i j:E)=> D (frame F i) (frame F j)
    let Q(D:AxisChart G F→L[ℝ] AxisChart G F→L[ℝ]ℝ):= (L D).det
    have hv : ContDiff ℝ ω Q:=by
         unfold Q L; simp_rw [Matrix.det_apply]; refine ContDiff.sum fun σ _=> ?_; simp only [Units.smul_def]
         refine ContDiff.const_smul _ (contDiff_prod ?_)
         intro i hi; exact ((contDiff_id.clm_apply contDiff_const).clm_apply contDiff_const)
    have hu(D:PathData G)(x:VChart G F): hessian F t p D x.1 x.2=L (f D x):=by ext i j; rw [hessian,Matrix.of_apply, iteratedFDeriv_two_apply]; rfl
    exact (X.forecast.forecast.compose hv.contDiffAt).ferry (Eventually.of_forall fun x=> congr_arg Matrix.det (hu P x).symm) (Eventually.of_forall fun i=>Eventually.of_forall fun x=> congr_arg Matrix.det (hu _ x).symm)

lemma steam {O:ChartRatio G}(hO: LocalRatio O)(hw:0<η)(t:S.Choices): View (fun i=> thermal F t p (R i) (r i) O) (thermal F t p P u O) 0 0:=by
    have D:=dreams h he hp hw; have hf:View (fun i=>WilsonStartup.Change.graph (r i)) (WilsonStartup.Change.graph u) 0 0:= (View.checked (F:=id) (x:=fun _=>0) contDiffAt_id tendsto_const_nhds).twins D
    have hQ : (WilsonStartup.Change.graph u) 0=0:= (station_of hp t).at0; have hV : (fun _=>0) =ᶠ[atTop] fun i=>WilsonStartup.Change.graph (r i) 0:= he.mono fun i hi=> (station_of hi.1 t).at0.symm
    let A(P:PathData G)(x: VChart G F):= Precision.loop P (readFine F x)
    have hz: View (fun i=> A (R i)) (A P) 0 0:=by
         let V (x:VChart G F):= readFine F x; obtain ⟨x,hX,hT,hV⟩:=reverse_run V (readFine_one _) (readFine_diff _)
         have hh : View (fun i=>turnSeries (R i|>.loop) (m:=m)) (turnSeries P.loop) (fun i=> x (0:VChart G F)) (x 0):=by rw [hX]; exact h.harvest.2
         exact ((View.checked (x:=fun _=>0) hT (tendsto_const_nhds (f:=atTop))).comp hh).ferry (hV.fun_comp (Precision.loop P)) (Eventually.of_forall fun i=>hV.fun_comp (Precision.loop (R i)))
    let Q(U: AxisChart G F):= Real.log (∏ i,O.J (U i))
    have hX: ContDiffAt ℝ ω Q (u 0):=by
         rw [hp.1]; unfold Q; refine (ContDiffAt.log (f:=fun U: AxisChart G F=> ∏ i,O.J (U i)) (contDiffAt_prod ?_) (by simp [hO.anchored])) -- fix
         intro i _; exact (hO.germ _ (by simpa using hO.patch)).comp _ (contDiff_apply ℝ _ i|>.contDiffAt)
    let M(P: PathData G)(x: VChart G F):= (hessian F t p P x.1 x.2).det
    have hM:View (fun i=> M (R i)) (M P) (fun i=>WilsonStartup.Change.graph (r i) 0) ((WilsonStartup.Change.graph u) 0) := hQ.symm ▸ ((mirrorB (hp:=hp) h he t).points hV)
    have hm : ContDiffAt ℝ ω Real.log (M P (WilsonStartup.Change.graph u 0)) := Real.contDiffAt_log.mpr (Work.F05.hessian_pos hw (hatch h he) hp t|>.self_of_nhds |>.ne')
    exact ((hf.comp (hQ.symm ▸ hz.points hV)).plus (((hf.comp hM).compose hm).coin (1/2:ℝ))).tune (D.compose hX)
end YM.Stationary.Beacon
