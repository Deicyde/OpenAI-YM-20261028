import YM.TraceExtension.Atlas.Chalk
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set
open scoped Topology BigOperators ContDiff
section
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][FiniteDimensional ℂ E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E]
open ContinuousLinearMap
local notation "M₀" => E →L[ℂ] E
private lemma square_progress {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V][CompleteSpace V](M:V→V→V)(hA:∀ x:V, IsLinearMap ℝ (M x))(hB:∀ y:V,IsLinearMap ℝ (fun x=>M x y))(a:V)(h:∀ x, M x a=x)(h₀:∀ x,M a x=x)(f:ℕ→V)(hf:Tendsto f atTop (𝓝 a)): ∃ p:ℕ→V,Tendsto p atTop (𝓝 a) ∧ ∀ᶠ i in atTop,M (p i) (p i)=f i:=by
    let f'(x:V): V→L[ℝ] V:=LinearMap.toContinuousLinearMap (IsLinearMap.mk' _ (hA x));
    let P:V→ₗ[ℝ] V→L[ℝ] V := {
        toFun:=f'
        map_add':= fun x y=> ContinuousLinearMap.ext (fun i=> (hB i).map_add ..)
        map_smul':=fun t x=> ContinuousLinearMap.ext (fun i=> (hB i).map_smul ..) }
    let Q:= LinearMap.toContinuousLinearMap P;
    let v:V≃L[ℝ] V:= ContinuousLinearEquiv.smulLeft (Units.mk0 (2:ℝ) (by norm_num))
    let F' := fun x:V=> M x x
    have hp: HasStrictFDerivAt F' (v:V→L[ℝ] V) a:=by
        have he:= hasStrictFDerivAt_id (𝕜:=ℝ) a
        convert Q.hasStrictFDerivAt_of_bilinear he he using 1
        · rfl
        ext1 i; change (2:ℝ) • i=M a i+M i a; rw[h,h₀,two_smul]
    have hh : Tendsto f atTop (𝓝 (F' a)):=by unfold F'; rw[h]; exact hf
    let p:= hp.localInverse F' v a ∘ f
    exact ⟨p,hp.localInverse_tendsto.comp hh,hh.eventually hp.eventually_right_inverse⟩
lemma bridgeO [FiniteDimensional ℝ E] (U:Submodule ℝ (M₀)) (he : (1:M₀)∈U)(hf: ∀ x y: U,x.val*y.val∈U)(f:ℕ→U) (hp:Tendsto f atTop (𝓝 (⟨1,he⟩:U))):∃ g:ℕ→U,Tendsto g atTop (𝓝 (⟨1,he⟩:U)) ∧ ∀ᶠ i in atTop, (g i).val*(g i).val=(f i).val∧IsUnit ((g i).val):=by
    letI : FiniteDimensional ℝ (M₀):= Module.Finite.trans ℂ _; letI: CompleteSpace U:= FiniteDimensional.complete ℝ _
    let a:U:= ⟨1,he⟩
    let M(x y: U):U:= ⟨x.val*y.val,hf x y⟩
    have hA(x:U):IsLinearMap ℝ (M x):=by
       constructor;intro i j
       · apply Subtype.ext; exact mul_add x.val i.val j.val
       intro t i; apply Subtype.ext;exact mul_smul_comm ..
    have hB(y:U): IsLinearMap ℝ (fun x=>M x y):=by
       constructor; intro i j
       · apply Subtype.ext;exact add_mul i.val j.val y.val
       intro t i;apply Subtype.ext;exact smul_mul_assoc ..
    obtain ⟨p,hx,hp⟩:= square_progress M hA hB a (fun x=>Subtype.ext (mul_one _)) (fun x=>Subtype.ext (one_mul _)) f hp
    have hw:Tendsto (fun i=>(p i).val) atTop (𝓝 1):=continuous_subtype_val.continuousAt.tendsto.comp hx
    exact ⟨p,hx,(hp.and (hw.eventually (Units.isOpen.mem_nhds isUnit_one))).mono fun i hi=>⟨congr_arg Subtype.val hi.1,hi.2⟩⟩
end
end YM.Trace.Pilot
