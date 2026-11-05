import YM.TraceExtension.Terrace.Look
import YM.TraceExtension.Anchor.Persist
import YM.TraceExtension.Prom.Zoom.Running
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}
section limit
/- The right setting for recording a stencil insertion before taking its IR limit and
 then changing the physical basis. Use ONE common ultrafilter. No stronger assertion of
 unique period limit for any of these auxiliary matrices. -/
variable {C:Family G} {F: Extraction.Order} {𝓛: Ultrafilter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "a!"=> (𝓛:Filter (ℕ×ℕ))
local notation "A"=> C.path.levels
variable (hb: (𝓛:Filter (ℕ×ℕ)) ≤ F.fuse)
include hb
lemma link_period : Tendsto Prod.snd (𝓛:Filter (ℕ×ℕ)) atTop:=by
   apply Tendsto.mono_left _ hb
   apply tendsto_atTop.2; intro b
   rw[F.fused];change ∀ᶠ i:ℕ in atTop,∀ᶠ j:ℕ in atTop,b ≤ F.per i
   exact (F.per.cofinal.eventually_ge_atTop _).mono (fun j h=>Eventually.of_forall fun i=>h)
lemma link_mesh : Tendsto Prod.fst (𝓛:Filter (ℕ×ℕ)) atTop:= tendsto_atTop.2 (fun i=> (large_mesh F i).filter_mono hb)
omit hb in
lemma crewing {T:Type*}[NormedAddCommGroup T][ProperSpace T] {Px:Type*}(f:Px→T)(b:ℝ)(L:Ultrafilter Px) (ht:∀ᶠ j in (L:Filter Px), ‖f j‖ ≤ b): ∃ y:T,Tendsto f (L: Filter Px) (𝓝 y):=by
   obtain ⟨k,h,hK,p,hp⟩:= finite_extract f b (𝓛:=(L:Filter _)) ht; have hx:= L.unique h; subst k;exact ⟨p,hp⟩
variable (H:C.Makes) {d m j k:ℕ}
local notation "D!"=>C.labels.level d
omit hb H in
lemma continu (D : Frame G d): Continuous D.coeffSize:=by unfold Frame.coeffSize;fun_prop
include H
lemma mint (k:ℕ):∃ z:ℝ, Tendsto (fun j:ℕ×ℕ=> C.path.β j.1 j.2 k) a! (𝓝 z):=by
   let P:=C.path; let y(i:ℕ×ℕ):= P.β i.1 i.2 k; let x:=(A).clock.hatBeta k
   refine crewing y (2*x) _ ?_
   filter_upwards [(link_mesh hb).eventually_ge_atTop k] with i hi
   have h : k ≤ i.1:=hi; have hh:(A).clock.hatBeta k /2 ≤ y i∧ y i ≤ 2*x:=(H.wilson.represents i.1 i.2 k hi).band
   rw[Real.norm_of_nonneg ((half_pos (bell ..)).le.trans hh.1)]; exact hh.2
lemma term_limits (hk:C.ref d ≤ k): ∃ X:C.label d ≃ₗ[ℂ] C.label d,∀ (v:ℕ×ℕ→C.label d)(z:C.label d),Tendsto v a! (𝓝 z) → Tendsto (fun j:ℕ×ℕ=> Cturn C d k j.1 j.2 (v j)) a! (𝓝 (X z)):=by
   let U(i:ℕ×ℕ): C.label d →ₗ[ℂ] C.label d:= if h:k ≤ i.1 then (nib_linear _ H (p:=i.2) hk h).mk' _ else 0
   have he:{i:ℕ×ℕ|k ≤ i.1}∈ a! := (link_mesh hb).eventually_ge_atTop k
   have hu(i:ℕ×ℕ)(hk:k ≤ i.1)(v) : U i v=Cturn C d k i.1 i.2 v:=by unfold U; rw[dif_pos hk];rfl
   let B:= (Real.exp (Work.D01.columnLogs (A) k))*(Fintype.card (D!).Index)
   have hB : ∀ᶠ i in a!, ‖LinearMap.toContinuousLinearMap (U i)‖≤B:=by
       filter_upwards [he] with i hi
       refine ContinuousLinearMap.opNorm_le_bound _ (show 0 ≤ B from by unfold B; positivity) (fun x=>?_)
       change ‖U i x‖ ≤ _; rw[hu i hi];
       refine (Push.RelayDifference.norm_cost (D!) _).trans ((Work.D01.back_budget C H x hk hi (p:=i.2)).trans ?_)
       unfold B; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
       simpa only [Frame.coeffSize,nsmul_eq_mul] using! Pi.sum_norm_apply_le_norm (G:=fun _: (D!).Index=>ℂ) x
   obtain ⟨Z,hZ⟩:= crewing _ B 𝓛 hB
   let Y:= Z.toLinearMap; have hp(v:ℕ×ℕ→ C.label d)(z:C.label d)(h:Tendsto v a! (𝓝 z)): Tendsto (fun j:ℕ×ℕ=>Cturn C d k j.1 j.2 (v j)) a! (𝓝 (Y z)):= (Dash.arcing hZ h).congr' ((show ∀ᶠ i in a!, U i (v i)=Cturn C d k i.1 i.2 (v i) from by filter_upwards [he] with i hi;exact hu i hi (v i)))
   have hI: Injective Y:=by
        apply LinearMap.ker_eq_bot.mp; refine LinearMap.ker_eq_bot'.mpr fun v he'=>?_
        apply Work.G08.size_separates
        have hs:=hp (fun _=>v) v tendsto_const_nhds; rw [he'] at hs
        let ξ(i:ℕ×ℕ):=outward C d k*(D!).coeffSize (Cturn C d k i.1 i.2 v)
        have hz: Tendsto ξ a! (𝓝 (0:ℝ)):=by simpa only [Frame.coeffSize,Pi.zero_apply,norm_zero,Finset.sum_const_zero,mul_zero,ξ,comp_apply] using! (((continu (D!)).continuousAt.tendsto.comp hs).const_mul (outward C d k))
        refine ge_of_tendsto hz ?_; filter_upwards[he] with i hI using at_current C H hk hI i.2 v
   exact ⟨LinearEquiv.ofBijective Y ⟨hI, LinearMap.injective_iff_surjective.mp hI⟩,hp⟩
omit hb H
/-- Auxiliary charts; not components of phase decomposition. -/
structure Arch (C:Family G) where
   β : ℕ → ℝ
   M (d k :ℕ): C.label d ≃ₗ[ℂ] C.label d
structure steep (𝓛: Ultrafilter (ℕ×ℕ))(Z: Arch C) :Prop where
   mintS (i:ℕ):Tendsto (fun j:ℕ×ℕ=> C.path.β j.1 j.2 i) (𝓛:Filter (ℕ×ℕ)) (𝓝 (Z.β i))
   terms (d k:ℕ) : C.ref d ≤ k → ∀ (v:ℕ×ℕ → C.label d)(z:C.label d),Tendsto v (𝓛:Filter (ℕ×ℕ)) (𝓝 z) → Tendsto (fun i:ℕ×ℕ=> Cturn C d k i.1 i.2 (v i)) (𝓛:Filter (ℕ×ℕ)) (𝓝 (Z.M d k z))
include hb H
lemma styling : ∃ Z:Arch C, steep 𝓛 Z:=by
    choose x h using fun i=> mint hb H i
    let U d k:= if h:C.ref d ≤ k then Classical.choose (term_limits hb H h) else LinearEquiv.refl ℂ _
    refine ⟨⟨x,U⟩,⟨h,fun d k hk=>?_⟩⟩; dsimp only[U]; rw [dif_pos hk]; exact Classical.choose_spec (term_limits hb H hk)

variable {Z:Arch C}(hZ: steep 𝓛 Z)
include hZ
lemma holds (k:ℕ) : (A).clock.hatBeta k/2 ≤ Z.β k ∧ Z.β k ≤ 2*(A).clock.hatBeta k:=by
    have hx:= hZ.mintS k; have hp:= ((link_mesh hb).eventually_ge_atTop k).mono (fun i hi=> (H.wilson.represents i.1 i.2 k hi).band)
    exact isClosed_Icc.mem_of_tendsto hx hp
lemma measured(k:ℕ): 0 < Z.β k:= lt_of_lt_of_le (half_pos (bell ..)) (holds hb H hZ k).1
lemma dex (k:ℕ) : Z.β k ≤ 2*(A).clock.hatBeta k:= (holds hb H hZ k).2
lemma cure (h:G.Simple): Tendsto Z.β atTop atTop:= tendsto_atTop_mono (fun i=> (holds hb H hZ i).1) ((hrate (A) h).atTop_div_const (show 0<(2:ℝ) by norm_num))
lemma Merr : ∀ ε:ℝ,0<ε → ∀ᶠ i:ℕ in atTop, |Z.β i-(A).clock.hatBeta i| ≤ ε*C.S.scale i:=by
    intro ε hε; filter_upwards [H.wilson.running ε hε] with i hv
    have hx:= (hZ.mintS i).sub_const ((A).clock.hatBeta i)
    exact le_of_tendsto (Continuous.tendsto continuous_abs _|>.comp hx) (((link_mesh hb).eventually_ge_atTop i).mono fun j h=> hv _ _ h)
lemma gamut (h:G.Simple) : Tendsto (fun i=>Z.β i/(A).clock.hatBeta i) atTop (𝓝 1):=by
    apply Metric.tendsto_nhds.mpr; intro ε hε
    have hp:= Gauge.slopeConstant_pos h
    filter_upwards [Merr hb H hZ (ε*G.slopeConstant) (mul_pos hε hp)] with i hi
    let s:= Z.β i; let x:= (A).clock.hatBeta i; have hx:0<x:=bell ..; have hz: G.slopeConstant*C.S.scale i<x:=lt_add_of_pos_left _ (A).clock.bar_pos
    change dist (s/x) 1 < ε
    rw[Real.dist_eq,div_sub_one hx.ne',abs_div,abs_of_pos hx]; exact (div_lt_iff₀ hx).2 (hi.trans_lt (by rw [mul_assoc];exact mul_lt_mul_of_pos_left hz hε))
end limit
end YM.Trace.Terrace
