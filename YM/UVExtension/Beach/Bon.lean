import YM.UVExtension.Beach.Rolls
/-! # Compact-sector Vitali savings. Norm convergence even for space arrays on Lab. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Metric Lattice RG Wilson
open Extraction Fallow Poppy Tide Swell Lamppost Spire Pier Rafter BoundedContinuousFunction
open scoped Topology BigOperators Classical ContDiff
variable {a:ℝ}
local notation "V"=> Row a
local notation "Z"=> ball (0:ℂ) a
section lift
variable {I E : Type} [NormedAddCommGroup E][NormedSpace ℂ E] [CompleteSpace E] {x:ℂ} (u:E→L[ℂ]ℂ) (f:ℂ→ E)
lemma motes (H:DifferentiableOn ℂ f Z)(hx:x∈ Z)(m:ℕ) : iteratedDeriv m (fun z=> u (f z)) x= u (iteratedDeriv m f x):=by
   induction m generalizing x with
   | zero=> simp
   | succ i ih=>
     rw [iteratedDeriv_succ,iteratedDeriv_succ]; have hp: DifferentiableAt ℂ (iteratedDeriv i f) x:=by rw [iteratedDeriv_eq_iterate]; exact (((H.analyticAt (isOpen_ball.mem_nhds hx)).iterated_deriv i).differentiableAt)
     exact (u.hasFDerivAt.comp_hasDerivAt x hp.hasDerivAt|>.congr_of_eventuallyEq (Eventually.mono (p:=fun x:ℂ=> x∈Z) (isOpen_ball.mem_nhds hx) (fun x hx=>ih hx))).deriv -- filter syntax

-- Reader. given cap on chart domain. uniform.K-only.
variable [TopologicalSpace I] [DiscreteTopology I] (ha:0<a)(F:ℕ→ ℂ→ I→ℂ)(Y: Row a→ (I →ᵇ ℂ)){m:ℝ}
variable (hk:∀ᶠ i in atTop,(∀ x:I,DifferentiableOn ℂ (fun z=> F i z x) (Metric.ball (0:ℂ) a))∧ (∀ z∈Metric.ball (0:ℂ) a,∀ x:I,‖F i z x‖≤ m))(hm:0 ≤ m)(ht:∀ d:Row a,TendstoUniformly (fun i (s:I)=> F i (d.val:ℂ) s) (Y d) atTop)
include ha hk hm ht
lemma accents: ∃ f:ℂ→(I →ᵇ ℂ),DifferentiableOn ℂ f Z∧ (∀ z∈ Z, ‖f z‖ ≤ m) ∧ (∀ d:Row a, f d.val=Y d)∧∀ j:ℕ, ∀ K:Set ℂ,IsCompact K→ K⊆ Z →∀ ε:ℝ, 0<ε →∀ᶠ i:ℕ in atTop,∀ z∈ K,∀ x:I,‖iteratedDeriv j (fun v=> F i v x) z- (iteratedDeriv j f z) x‖< ε:=by
   obtain ⟨n,hn⟩ := eventually_atTop.mp hk; let G(i:ℕ)(z:ℂ): I →ᵇ ℂ:= if h:n ≤ i ∧ z∈ Z then ofNormedAddCommGroupDiscrete (fun x=>F i z x) m (hn i h.1|>.2 z h.2) else 0
   have he(i)(h:n≤ i)(z)(hz:z∈Z)(x:I): G i z x=F i z x:=by unfold G; rw [dif_pos (And.intro h hz)]; rfl
   have hK (i): DifferentiableOn ℂ (G i) Z ∧ ∀ z∈ Z, ‖G i z‖≤ m:=by
       by_cases h:n ≤ i; swap; · simp only [G,h,false_and, ↓reduceDIte,norm_zero]; exact ⟨differentiableOn_const _,fun _ _=> hm⟩
       have hv(z)(hz:z∈Z)(x): ‖G i z x‖ ≤ m:= (he i h z hz x).symm ▸ (hn _ h|>.2) z hz x
       have hp : Bumps Z (G i):= canal (fun x=> bumps _ (fun z=> G i z x) ((hn i h|>.1 x).congr (fun z hz=> he i h z hz x))) hv hm
       exact ⟨hp _ id isOpen_ball (mapsTo_id _) differentiableOn_id,fun z hz=> (BoundedContinuousFunction.norm_le hm).2 (hv z hz)⟩
   let hq(d:Row a): (↑d.val:ℂ)∈ Z:= desk a ha|>.within d
   have hp(d:Row a): Tendsto (fun i=>G i d.val) atTop (𝓝 (Y d)):=by
       refine Metric.tendsto_nhds.mpr (fun ε hx=>?_); filter_upwards [Metric.tendstoUniformly_iff.mp (ht d) (ε/2) (half_pos hx),eventually_ge_atTop n] with i hi hh
       refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hx|>.le)).2 (fun x=>?_)) (half_lt_self hx); rw [he _ hh _ (hq _) _,dist_comm]; exact (hi x).le
   obtain ⟨f,hV,hX⟩:= Camp.viva a ha m hK (fun d hd=> ⟨_,hp ⟨d,hd⟩⟩)
   have hY:TendstoLocallyUniformlyOn G f atTop Z:=by simpa using! hX 0
   refine ⟨f,hV.differentiableOn,fun z hz=> le_of_tendsto (hY.tendsto_at hz|>.norm) (Eventually.of_forall (fun i=> hK i|>.2 z hz)), fun d=>tendsto_nhds_unique (hY.tendsto_at (hq d)) (hp d),fun j K hk hs ε he'=>?_⟩
   have hg:= tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball |>.1 (hX j) K hs hk; filter_upwards [Metric.tendstoUniformlyOn_iff.mp hg ε he',eventually_ge_atTop n] with i hi h z hz x
   let u: (I→ᵇ ℂ) →L[ℂ] ℂ:= evalCLM ℂ x
   rw [show iteratedDeriv j (fun t=> F i t x) z= u (iteratedDeriv j (G i) z) from ?_]; apply lt_of_le_of_lt ((iteratedDeriv j (G i) z- iteratedDeriv j f z).norm_coe_le_norm x) ?_; rw [← dist_eq_norm,dist_comm]; exact hi z hz
   refine Eq.trans ?_ (motes u (G i) (hK i|>.1) (hs hz) j); exact (show (fun t=> F i t x) =ᶠ[𝓝 z] (fun t=> u (G i t)) from Eventually.mono (isOpen_ball.mem_nhds (hs hz)) (fun a ha=> (he i h a ha x).symm)).iteratedDeriv_eq j -- needs x
end lift
end YM.UVExtension.Beach
