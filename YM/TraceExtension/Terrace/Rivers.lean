import YM.TraceExtension.Terrace.Insert
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set MeasureTheory NormedRing
open scoped BigOperators Topology ContDiff
-- recovered basis operators from one triangle of sensor prices
lemma revise {R E:Type*}[RCLike R] [NormedAddCommGroup E] [NormedSpace R E][FiniteDimensional R E] {H:Type*}[NormedAddCommGroup H][NormedSpace R H] [FiniteDimensional R H]
    (v:ℕ→E→L[R] E) (w:ℕ→ E→L[R] H) (T:E →L[R] H) (hv:Tendsto v atTop (𝓝 1))(hw:Tendsto (fun i=>(w i).comp (v i)) atTop (𝓝 T)) : Tendsto w atTop (𝓝 T):=by
    haveI : CompleteSpace E:= FiniteDimensional.complete R E
    have hs:Tendsto (Ring.inverse ∘ v) atTop (𝓝 1):=by simpa using (NormedRing.inverse_continuousAt (1:(E→L[R] E)ˣ)).tendsto.comp (show Tendsto v atTop (𝓝 ((1:(E→L[R] E)ˣ): (E→L[R] E))) from hv)
    have he : IsUnit (1:E→L[R] E):= isUnit_one
    have hu:= hv.eventually ((show IsOpen {x : (E→L[R] E) | IsUnit x} from ?_).mem_nhds he); swap; · rw [show {x : (E→L[R] E) | IsUnit x}=Set.range (Units.val : (E→L[R] E)ˣ → _) from ?_]; exact Units.isOpen; ext; simp[IsUnit]
    have hm:T.comp (1:E→L[R] E)=T:=rfl
    rw [←hm]; refine Tendsto.congr' ?_ (( (show Continuous (fun p : (E→L[R] H) × (E→L[R] E) => p.1.comp p.2) from continuous_fst.clm_comp continuous_snd)).continuousAt.tendsto.comp (hw.prodMk_nhds hs))
    filter_upwards [hu] with i hi; obtain ⟨x,hx⟩:= (show IsUnit (v i) from hi);
    change ((w i).comp (v i)).comp (Ring.inverse (v i))=w i; rw [← hx,ContinuousLinearMap.comp_assoc];
    rw [show (x: E→L[R] E).comp (Ring.inverse (x: E→L[R] E))=1 from by change (x:E→L[R] E)*_=1; simp]; rfl

variable {G:Gauge}
end YM.Trace.Terrace
