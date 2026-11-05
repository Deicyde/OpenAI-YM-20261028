import YM.TraceExtension.Terrace.Dusk
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G} {F: Extraction.Order} {𝓛: Ultrafilter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "a!"=> (𝓛:Filter (ℕ×ℕ))
local notation "A"=> C.path.levels
variable {Z:Arch C}(hZ: steep 𝓛 Z) {d m j k:ℕ}
local notation "D!"=> C.labels.level d
/-- price orientation in retained representation. -/
def swale (Z:Arch C)(d i:ℕ): Module.End ℂ (C.label d):= (((C.path.levels.budget i).threshold^ (2:ℕ))⁻¹:ℝ) • ((C.labels.level d).core.comp (Z.M d i).toLinearMap)
lemma land(k:ℕ)(v:C.label d): swale Z d k v=((C.path.levels.budget k).threshold^ (2:ℕ))⁻¹ • (D!).core (Z.M d k v):=rfl
include hZ
lemma topPitch(h:C.ref d ≤ k){v:ℕ×ℕ→C.label d}{w}(hw:Tendsto v a! (𝓝 w)) : Tendsto (fun j:ℕ×ℕ=> spine C d k j.1 j.2 (v j)) a! (𝓝 (swale Z d k w)):=by
    exact tendsto_const_nhds.smul ((LinearMap.toContinuousLinearMap ((D!).core)).continuous.continuousAt.tendsto.comp (hZ.terms _ _ h _ _ hw))
variable (H:C.Makes) (hb: (𝓛:Filter (ℕ×ℕ))≤ F.fuse)
include H hb
lemma move_anchor_unit (hk:C.ref d ≤ k) : (Z.M d k) (C.refUnit d)=unitVec (D!) C.path k:=tendsto_nhds_unique_of_eventuallyEq (hZ.terms _ _ hk (fun _=> C.refUnit d) _ tendsto_const_nhds) tendsto_const_nhds (((link_mesh hb).eventually_ge_atTop k).mono fun i hi=> nib_unit C H hk hi)
lemma Barry(hG:G.Simple)(θ:PostT C.path.levels): Tendsto (fun i=> Z.β i/Z.β (summit (A) i)) atTop (𝓝 1) := by
   let t:= summit (A); let s:= G.slopeConstant; let x:= (A).clock.hatBeta; let P i:=gap (A) i (t i)
   have ht : Tendsto (fun i=>P i/x i) atTop (𝓝 0):=by
       have hv:=Gate_calm.comp (hrate (A) hG); refine squeeze_zero' ?_ (g:=fun i=>2*(Gate (x i)/x i)) ?_ (by simpa only [mul_zero] using! hv.const_mul 2);
       · refine Eventually.of_forall (fun i=>?_); exact div_nonneg ((gate_le _ ((A).fits.delayed _)).le.trans (gstar ..)) (bell ..|>.le)
       filter_upwards [back_gate (A) hG θ] with i hi; rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hi (bell ..|>.le)
   have hp:Tendsto (fun i=> x (t i)/x i) atTop (𝓝 1):=by
      have he(i): x (t i)/x i=1+s*(P i/x i):=by unfold x; rw [stamps (A) i (t i),add_div,div_self (bell (A) i|>.ne')]; rw [← mul_div_assoc]
      simp_rw[he]; simpa only[mul_zero,add_zero] using (ht.const_mul s).const_add 1
   let K:=Z.β; have hQ : Tendsto (fun i=> K (t i)/x i) atTop (𝓝 1):=by
       have hu:Tendsto (fun i=> K (t i)/x (t i)) atTop (𝓝 1):= (gamut hb H hZ hG).comp (Sstar (A)); have hx := hu.mul hp
       have he (i): K (t i)/x (t i)*(x (t i)/x i)=K (t i)/x i:=by have hy:x (t i)≠0:=(bell ..).ne'; field_simp
       simpa only[he,mul_one] using! hx
   have he(i): (Z.β i)/(Z.β (summit (A) i))=(Z.β i/x i)/(Z.β (t i)/x i):=by change K i/K (t i)= _; have hx:x i≠0:=(bell ..).ne'; field_simp;rfl
   simp_rw[he]; simpa only[div_one] using! (gamut hb H hZ hG).div hQ one_ne_zero
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {ζ:ℕ→ℕ→ℝ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hr:Scrim C W u ψ φ δ ζ r D)
include hr
lemma move_anchor (hk:C.ref d ≤ k)(v:C.label d)(s:Signed): Z.M d k ((D!).act s.ortho v)= (D!).act s.ortho (Z.M d k v):=by
    have hp := hZ.terms _ _ hk (fun _=>v) _ tendsto_const_nhds
    exact tendsto_nhds_unique_of_eventuallyEq (hZ.terms _ _ hk (fun _=>(D!).act s.ortho v) _ tendsto_const_nhds) (((D!).act s.ortho).continuous_of_finiteDimensional.continuousAt.tendsto.comp hp) (((link_mesh hb).eventually_ge_atTop k).mono fun i hi=>(guarded C H hr hk hi v s).2)
lemma move_anchor_star (hk:C.ref d ≤ k)(v:C.label d): Z.M d k (star v)=star (Z.M d k v):=tendsto_nhds_unique_of_eventuallyEq (hZ.terms _ _ hk (fun _=>star v) _ tendsto_const_nhds) ((hZ.terms _ _ hk (fun _=>v) _ tendsto_const_nhds).star) (((link_mesh hb).eventually_ge_atTop k).mono fun i hi=>(guarded C H hr hk hi v 1).1)
lemma gateW (hk:C.ref 5 ≤ k)(v:C.label 5)(hv:night _ v): night _ (Z.M 5 k v):=by unfold night;rw [← move_anchor hZ H hb hr hk,hv,map_neg]
variable (K:Sceptre C W)(θ:PostT C.path.levels)(hG:G.Simple)
include K θ hG
omit hr H in
lemma evening :∀ᶠ i in atTop,let k:=summit C.path.levels i; let f:=C.labels.level 4; ∀ (v:C.label 4) (j:ℕ),i≤j→j≤k→ f.coeffSize (swale Z 4 j v-swale Z 4 k v) ≤ part C.path.levels i *f.coeffSize (swale Z 4 k v):=by
   filter_upwards [spine_pitch C W hG θ K 4 (by decide),eventually_ge_atTop (C.ref 4)] with i hi hj k f v j hv ht
   let V (j:ℕ): ℕ×ℕ→ C.label 4:=fun l=> spine C 4 j l.1 l.2 v; have hu j (he:i≤j): Tendsto (V j) a! (𝓝 (swale Z 4 j v)):= topPitch hZ (hj.trans he) (v:=fun _=>v) tendsto_const_nhds
   have hs := (((continu f).continuousAt.tendsto).comp (hu k (hv.trans ht))).const_mul (part (A) i)
   refine le_of_tendsto_of_tendsto (((continu f).continuousAt.tendsto).comp ((hu j hv).sub (hu k (hv.trans ht)))) hs ?_
   filter_upwards [(link_mesh hb).eventually_ge_atTop k,(link_period hb).eventually hi] with l hl he
   exact he _ hl v (fun _ _ _=> even_grade f hG _) j hv ht
lemma nightsE :∀ᶠ i in atTop,let k:=summit C.path.levels i; let f:=C.labels.level 5; ∀ (v:C.label 5) (j:ℕ),night f v→i≤j→j≤k→ f.coeffSize (swale Z 5 j v-swale Z 5 k v) ≤ part C.path.levels i *f.coeffSize (swale Z 5 k v):=by
   filter_upwards [spine_pitch C W hG θ K 5 (by decide),eventually_ge_atTop (C.ref 5)] with i hi hj k f v j hx hv ht
   let V (j:ℕ): ℕ×ℕ→ C.label 5:=fun l=> spine C 5 j l.1 l.2 v; have hu j (he:i≤j): Tendsto (V j) a! (𝓝 (swale Z 5 j v)):= topPitch hZ (hj.trans he) (v:=fun _=>v) tendsto_const_nhds
   have hs := (((continu f).continuousAt.tendsto).comp (hu k (hv.trans ht))).const_mul (part (A) i)
   refine le_of_tendsto_of_tendsto (((continu f).continuousAt.tendsto).comp ((hu j hv).sub (hu k (hv.trans ht)))) hs ?_
   filter_upwards [(link_mesh hb).eventually_ge_atTop k,(link_period hb).eventually hi] with l hl he
   exact he _ hl v (fun c hc hh=> night_grade f (night_space C H hr (hj.trans hc) (hh.trans hl) _ hx) hG) j hv ht
end YM.Trace.Terrace
