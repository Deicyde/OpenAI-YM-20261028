import YM.UVExtension.Beach.Bon
/-! # Strict local rates (including every coupling derivative) from
    Banach limits; return ordinary cont maps also from those.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Metric Lattice RG Wilson
open Extraction Fallow Poppy Tide Swell Lamppost Spire Pier Rafter BoundedContinuousFunction
open scoped Topology BigOperators Classical ContDiff
variable {a:ℝ}
local notation "V"=> Row a
local notation "Z"=> ball (0:ℂ) a
section
variable {I Y:Type} [TopologicalSpace I][CompactSpace I]
structure Key (I:Type) where val : I
instance : TopologicalSpace (Key Y):= ⊥
instance : DiscreteTopology (Key Y):= discreteTopology_bot _
def paper : (I →ᵇ ℂ) →L[ℂ] (Key I →ᵇ ℂ) :=by
   let g:ContinuousMap (Key I) I:=⟨Key.val,continuous_of_discreteTopology⟩
   exact ⟨⟨⟨fun F=>F.compContinuous g,fun _ _=>rfl⟩,fun _ _=>rfl⟩,continuous_compContinuous _⟩
lemma toll (V': I →ᵇ ℂ): ‖paper V'‖ = ‖V'‖:=by
    apply le_antisymm <;> apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
    · exact fun i=> V'.norm_coe_le_norm i.val
    exact fun i=> (paper V').norm_coe_le_norm ⟨i⟩
variable (ha:0<a)(F:ℕ→ ℂ→ I→ℂ)(Q: Row a→ (I →ᵇ ℂ)){m:ℝ}
variable (hk:∀ᶠ i in atTop,(∀ x:I,DifferentiableOn ℂ (fun z=> F i z x) (Metric.ball (0:ℂ) a))∧ (∀ z∈Metric.ball (0:ℂ) a,∀ x:I,‖F i z x‖≤ m))(hm:0 ≤ m)(ht:∀ d:Row a,TendstoUniformly (fun i (s:I)=> F i (d.val:ℂ) s) (Q d) atTop)
include ha hk hm ht
lemma punches : ∃ f:ℂ→(I →ᵇ ℂ),DifferentiableOn ℂ f Z∧ (∀ z∈ Z, ‖f z‖ ≤ m) ∧ (∀ d:Row a, f d.val=Q d)∧∀ j:ℕ, ∀ K:Set ℂ,IsCompact K→ K⊆ Z →∀ ε:ℝ, 0<ε →∀ᶠ i:ℕ in atTop,∀ z∈ K,∀ x:I,‖iteratedDeriv j (fun v=> F i v x) z- iteratedDeriv j (fun v=> f v x) z‖< ε:=by
   let Y'(d:Row a):= paper (Q d); have h(d:Row a): TendstoUniformly (fun i (s:Key I)=>F i (d.val:ℂ) s.val) (Y' d) atTop:= fun S hS=> ((ht d) S hS).mono (fun i hi s=> hi s.val)
   obtain ⟨f,hf,hF,hB,h⟩:= accents ha (fun i z x=> F i z (x:Key I).val) Y' (hk.mono fun i hi=> ⟨fun x=>hi.1 x.val,fun z hz x=>hi.2 z hz x.val⟩) hm h
   have hh(S:Finset (Row a))(p: Row a→ℂ): ‖∑ i∈S,p i • Q i‖ ≤ 1* ‖∑ i∈S,p i • f (desk a ha|>.call i)‖:=by
      have hx(i): f (desk a ha|>.call i)= Y' i:= hB i
      simp_rw [hx,Y',← map_smul,←map_sum,toll,one_mul]; exact le_rfl
   obtain ⟨g,hg,hv,hg'⟩:=reflectV (desk a ha) Q f (bumps _ _ hf) 1 zero_le_one hh; have hG : DifferentiableOn ℂ g Z:= hg Z id isOpen_ball (mapsTo_id _) differentiableOn_id
   have he x:EqOn (fun z=>g z x) (fun z=>f z (⟨x⟩:Key I)) Z:=(desk a ha).agrees _ _ (bumps _ _ ((evalCLM ℂ x:(I→ᵇℂ)→L[ℂ]ℂ).differentiable.comp_differentiableOn hG)) (bumps _ _ ((evalCLM ℂ (⟨x⟩:Key I): (Key I→ᵇℂ)→L[ℂ]ℂ).differentiable.comp_differentiableOn hf)) fun d=> by change _ = f d.val _; rw [hB,hv]; rfl
   refine ⟨g,hG,fun z hz=>(hg' z hz).trans (by rw [one_mul]; exact hF z hz),hv,fun j K hk ht ε hε=>(h j K hk ht ε hε).mono (fun i hi z hz x=>?_)⟩
   have he : (fun v=>g v x) =ᶠ[𝓝 z] fun v=> f v (⟨x⟩:Key I):= Eventually.mono (p:=fun t=> t∈Z) (isOpen_ball.mem_nhds (ht hz)) fun _ hv=> he _ hv
   rw [he.iteratedDeriv_eq j]; change ‖_- iteratedDeriv j (fun v=> evalCLM ℂ (⟨x⟩:Key I) (f v)) z‖ < _; rw [motes _ f hf (ht hz) j]; exact hi z hz ⟨x⟩
end
section
variable {I:Type}[MetricSpace I][LocallyCompactSpace I] {A:Set I}(hA:IsOpen A)(ha:0<a)(F:ℕ→ ℂ→ I→ℂ)(Q: Row a→ I→ℂ)
variable (hh:∀ᶠ i in atTop,∀ x:I,DifferentiableOn ℂ (fun z=> F i z x) (Metric.ball (0:ℂ) a))(hm:∀ K:Set I,K⊆A→ IsCompact K→ ∃ m:ℝ,0 ≤ m∧∀ᶠ i in atTop,∀ z:ℂ, z∈Metric.ball (0:ℂ) a→∀ x∈ K,‖F i z x‖≤ m) (hx:∀ d:Row a, Meets A (fun i=> F i d.val) (Q d))
-- For each compact ordinary continuous holomorphic lift.Limits. despite initial mesh functions not continuous.Ag
structure Stamp (a:ℝ)(X:Set I)(f:ℂ→I→ℂ)(U:ℕ→ ℂ→ I→ℂ) : Prop where
   analytic (x:I) (hx:x∈X): AnalyticOnNhd ℂ (fun z=>f z x) (Metric.ball 0 a)
   debt (S:Set I)(h:S⊆ X)(hp:IsCompact S):∃ g:ℂ→((S)→ᵇℂ),AnalyticOnNhd ℂ g (Metric.ball 0 a) ∧ (∃ b:ℝ, ∀ z∈ Metric.ball (0:ℂ) a,‖g z‖≤ b) ∧∀ x:S,EqOn (fun z=> f z x.val) (fun z=> g z x) (Metric.ball (0:ℂ) a)
   converges (K:Set ℂ)(hK:IsCompact K) (hA:K⊆ Metric.ball 0 a)(S:Set I)(hs:IsCompact S) (ht:S⊆ X) (j:ℕ)(ε:ℝ) (he:0<ε): ∀ᶠ i:ℕ in atTop,∀ z∈K,∀ x∈S,‖iteratedDeriv j (fun v=>U i v x) z- iteratedDeriv j (fun v=> f v x) z‖< ε
include ha hh hx hm
private lemma stems (K:Set I)(hk:IsCompact K)(h:K⊆ A): ∃ f:ℂ→(K →ᵇ ℂ),AnalyticOnNhd ℂ f Z∧ (∃ m:ℝ,∀ z∈ Z, ‖f z‖ ≤ m) ∧ (∀ (d:Row a) (x:K), f d.val x=Q d x.val)∧∀ j:ℕ, ∀ J:Set ℂ,IsCompact J→ J⊆ Z →∀ ε:ℝ, 0<ε →∀ᶠ i:ℕ in atTop,∀ z∈ J,∀ x:K,‖iteratedDeriv j (fun v=> F i v x.val) z- iteratedDeriv j (fun v=> f v x) z‖< ε:=by
    obtain ⟨m,h₁,hM⟩:=hm K h hk; letI :CompactSpace K:= isCompact_iff_compactSpace.mp hk
    let P(i:Row a): K →ᵇ ℂ:= mkOfCompact (⟨fun x:K=> Q i x.val,continuousOn_iff_continuous_restrict.mp ((hx i).continuousOn.mono h)⟩:ContinuousMap _ _)
    let Z' i z (x:K):= F i z x.val
    have hp(d): TendstoUniformly (fun i (x:K)=> F i (↑(d:Row a).val) x.val) (P d) atTop:= Metric.tendstoUniformly_iff.mpr fun ε he=> ((hx d).uniform K h hk ε he).mono fun i hi x=> (dist_comm _ _).trans_lt (hi _ x.2)
    obtain ⟨f,hf,hF,hT,hr⟩:= punches ha Z' P ((hh.and hM).mono fun i hi=> ⟨fun x=> hi.1 x.val,fun z hz x=> hi.2 z hz x.val x.2⟩) h₁ hp
    exact ⟨f,hf.analyticOnNhd isOpen_ball,⟨m,hF⟩,fun d x=> congr_arg (fun v:K→ᵇℂ=> v x) (hT d),hr⟩

lemma control :∃ f:ℂ→ I→ℂ, Stamp a A f F ∧ ∀ d:Row a,EqOn (f d.val) (Q d) A:=by
    have h(x)(hp:x∈A): ∃ f:ℂ→ℂ,AnalyticOnNhd ℂ f Z ∧∀ d:Row a,f d.val=Q d x:=by
       obtain ⟨f,hf,-,hQ,_⟩:= stems ha F Q hh hm hx {x} isCompact_singleton (Set.singleton_subset_iff.mpr hp)
       let q: (↑({x}:Set I)→ᵇℂ)→L[ℂ]ℂ:= evalCLM ℂ ⟨x,Set.mem_singleton _⟩; exact ⟨_, (q.differentiable.comp_differentiableOn hf.differentiableOn).analyticOnNhd isOpen_ball, fun d=> hQ d ⟨x,by simp⟩⟩
    choose! f hf hF using h
    have he (K:Set I)(hK:K⊆A)(p:ℂ→(K→ᵇℂ))(hp:AnalyticOnNhd ℂ p Z)(hc:∀ (d:Row a)(x:K),p d.val x=Q d x.val)(x:K): EqOn (fun z=>f x.val z) (fun z=> p z x) Z:= (desk a ha).agrees _ _ (bumps _ (f x.val) (hf x.val (hK x.2)|>.differentiableOn)) (bumps _ _ ((evalCLM ℂ x:(K→ᵇℂ)→L[ℂ]ℂ).differentiable.comp_differentiableOn hp.differentiableOn)) fun d=> (hF x.val (hK x.2) d).trans (hc d x).symm
    refine ⟨fun z x=> f x z,⟨hf,fun K hK h=>?_,fun K hk hK J hJ hj j ε h=>?_⟩,fun d x hx=> hF x hx d⟩
    · obtain ⟨g,hg,hQ,hG,-⟩:= stems ha F Q hh hm hx K h hK; exact ⟨g,hg,hQ,he K hK g hg hG⟩
    obtain ⟨g,hg,hQ,hG,H⟩:= stems ha F Q hh hm hx _ hJ hj; filter_upwards [H j K hk hK _ h] with i hi z hz x hx
    have hm : f x=ᶠ[𝓝 z] fun v=> g v ⟨x,hx⟩:= Eventually.mono (p:=fun v=>v∈Z) (isOpen_ball.mem_nhds (hK hz)) (fun _ h=> he J hj g hg hG ⟨x,hx⟩ h); try dsimp only
    rw [hm.iteratedDeriv_eq j]; exact hi z hz ⟨x,hx⟩
end
end YM.UVExtension.Beach
