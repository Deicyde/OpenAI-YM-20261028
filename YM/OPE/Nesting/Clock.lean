import YM.OPE.Nesting.Geometry

/-! Layer extraction along arbitrary refinements in the *continuum*
short-distance tail. T= sum log(1/s) over all vertices, so at least one
advancing edge always exists, not necessarily at the layer where a given
comparison is made. No log hierarchy is taken at fixed Wilson cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Tree
open Orbits Orbits.Reader Function Filter Extraction Set Table Measures Menu Atom MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {t:Tree}{s:t.Inner→ℝ}{z:t.Positions→E4}{α β r r' M η:ℝ}
-- clocks independent from the later basis:
lemma refine_cluster {X L:Type}[TopologicalSpace X]{f:L→X}{l:Filter L}{x:X}(hf:MapClusterPt x l f) : ∃ χ:Filter L, χ≤l ∧ χ.NeBot ∧ Tendsto f χ (𝓝 x) :=by
     refine ⟨l ⊓ comap f (𝓝 x),inf_le_left,?_,tendsto_comap.mono_left inf_le_right⟩
     refine _root_.Filter.neBot_iff.mpr fun ha=> ?_
     obtain ⟨u,hu,v,hv,empty⟩:=inf_eq_bot_iff.mp ha
     obtain ⟨p,hp,h⟩:=mem_comap.mp hv -- h shadow previous, fix
     have H:=mapClusterPt_iff_frequently.mp hf p hp
     obtain ⟨q,hq, hq'⟩:= (H.and_eventually (show ∀ᶠ i in l, i∈u from hu)).exists
     have hw: q ∈ u ∩ v := ⟨hq',h hq⟩
     exact notMem_empty q (empty ▸ hw)

lemma clock_compact {Z L:Type}[Fintype Z][Nonempty Z] {l:Filter L}[l.NeBot]{s:L→ Z→ℝ}
       (hs:∀ z:Z,Tendsto (fun i=> s i z) l (𝓝[>] 0)):
       ∃ χ:Filter L, χ≤l ∧ χ.NeBot ∧ ∃ T:L→ℝ, Tendsto T χ atTop ∧ ∃ a:Z→ℝ,
              (∑ z,a z)=1 ∧ ∀ v, RateIs χ T (fun i=> s i v) (-a v) := by
     let d(i)(z:Z):= run (s i z); let z₀:Z:=Classical.arbitrary Z
     have hd(z): Tendsto (fun i=>d i z) l atTop := run_towards (hs z)
     let T (i:L) : ℝ :=∑ z,d i z
     have h₁:∀ᶠ i in l,∀ v,d i v≥0:=eventually_all.mpr fun z=>(hd z).eventually_ge_atTop 0
     have h₂:∀ᶠ i in l,∀ v,d i v≤T i:=h₁.mono fun i he v=>single_le_sum (fun u _=>he u) (mem_univ v)
     have ht:Tendsto T l atTop:=tendsto_atTop_mono' l (h₂.mono fun _ h=> h z₀) (hd z₀) -- ≤ᶠ notation coe
     have ht':=ht.eventually_gt_atTop 0
     let x(i:L)(v:Z):ℝ:= d i v / T i; let Y:= {g:Z→ℝ|∀q,g q∈Set.Icc (0:ℝ) 1}
     have hh:map x l ≤ 𝓟 Y:=le_principal_iff.mpr (show ∀ᶠ g in l,x g∈Y from (h₁.and (h₂.and ht')).mono fun i ⟨h₁,h₂,hi⟩ v=> ⟨div_nonneg (h₁ v) hi.le,(div_le_one hi).2 (h₂ v)⟩)
     obtain ⟨a,ha,hP⟩:= (isCompact_pi_infinite (fun _:Z=> (isCompact_Icc (α:=ℝ)))).exists_mapClusterPt hh
     obtain ⟨χ,hχ,hh,htx⟩:=refine_cluster hP
     have h':=ht.mono_left hχ; have ht':=(ht.eventually_gt_atTop 0).filter_mono hχ
     have hv(v):Tendsto (fun i=>x i v) χ (𝓝 (a v)) := tendsto_pi_nhds.mp htx v
     have ht₁ : ∀ᶠ i in χ,∑ v,x i v=1:=ht'.mono (fun i hi=>by change ∑ j,d i j / T i=1; rw [← Finset.sum_div,show ∑ v:Z,d i v=T i from rfl, div_self (ne_of_gt hi)])
     refine ⟨χ,hχ,hh,T,h',a,(tendsto_nhds_unique_of_eventuallyEq (tendsto_finset_sum (s:=Finset.univ) (fun v _=>hv v)) tendsto_const_nhds ht₁), fun v=>?_⟩
     exact ⟨((hs v).mono_left hχ).eventually (self_mem_nhdsWithin : ∀ᶠ s:ℝ in 𝓝[>]0,0<s), (hv v|>.neg).congr (fun i=>by dsimp [x,d,run]; rw [neg_div,neg_neg])⟩

variable {L:Type}{l:Filter L}
lemma sizes_tend {r:L→ℝ}{s:L→t.Inner→ℝ}{β:ℝ}(hr:Tendsto r l (𝓝[>]0)) (ht:∀ᶠ i in l,t.Tapered (r i) β (s i)) (hβ:β≤1)(q:t.Inner): Tendsto (fun i=>s i q) l (𝓝[>]0) := tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (ht.mono fun i hi=> (hi.positive q).le) (ht.mono fun i hi=>hi.within hβ q) (tendsto_nhdsWithin_iff.mp hr|>.1), ht.mono fun i hi=>hi.positive q⟩
lemma clock_caps {r T:L→ℝ}{s:L→t.Inner→ℝ}{a:t.Inner→ℝ}{k:ℝ}[l.NeBot] (hT:Tendsto T l atTop)(ht:∀ᶠ i in l,t.Tapered (r i) 1 (s i))(hh:∀ v,RateIs l T (fun i=>s i v) (-a v))(hk:RateIs l T r (-k)):t.ordered k a:=by
     induction t generalizing k r with
     | bud=> exact True.intro
     | fork n f ih=>
          refine ⟨by_contra fun he=>?_,fun i=>ih i (ht.mono fun j hj=> by simpa only [mul_one] using (hj.2.2 i)) (fun p=> hh (Sum.inr ⟨i,p⟩)) (hh (Sum.inl ()))⟩
          have h': -a (Sum.inl ()) > -k:=neg_lt_neg (lt_of_not_ge he)
          obtain ⟨i,hi,hu⟩ := (ht.and ((hh (.inl ())).overtakes (hk.pays hT) hT h')).exists
          exact (not_le.mpr hu) hi.2.1

lemma clock_bound {T:L→ℝ}{s:L→t.Inner→ℝ}{a:t.Inner→ℝ}{z:Tree.Envelope L t}{k M η:ℝ}[l.NeBot]
      (hT:Tendsto T l atTop)(ht:∀ᶠ i in l,Relative M η t (s i) (z i))(hh:∀ v,RateIs l T (fun i=>s i v) (-a v))(hy:∀ v,Tendsto (fun i=>s i v) l (𝓝 0)) (hm:0≤M)(hη:0<η)(hc:t.ordered k a)(h₀:0≤k): Regular l T t k a z := by
     induction t generalizing k with
     | bud => exact h₀
     | fork n f ih=>
          have hp:=h₀.trans hc.1
          let r(i:L):= s i (Sum.inl ()); let δ:=a (Sum.inl ())
          have h₁:RateIs l T (fun i=>η*r i) (-δ):= by have h:=(RateIs.const hT hη).mul (hh (Sum.inl ())); simpa only [zero_add] using h
          have h₂: RateLE l T (fun i=>M*r i) (-δ):= ((RateLE.const M hT).mul ((hh (Sum.inl ())).pays hT)).mono (by rw [zero_add])
          have he:∀ᶠ i in l, ‖away (z i) (Tree.center z i)‖ ≤ M*r i:=ht.mono (fun i hi=> (pi_norm_le_iff_of_nonneg ((hi.1 (fork n f|>.topSeat) |>.trans' (norm_nonneg _)))).mpr hi.1) -- nonneg argument erroneously M extra
          have hr:Tendsto (fun i=>M*r i) l (𝓝 0):= (by simpa only [mul_zero] using (hy (Sum.inl ())|>.const_mul M)) -- target M*0 definal? no
          refine ⟨h₀,hc.1,h₂.of_norm_le he,tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) he hr),?_,?_⟩ -- k≤a should hc.1 only
          · intro i j hv u hu; filter_upwards [ht,h₁.overtakes (RateLE.exp (-u) hT) hT (neg_lt_neg hu)] with q h₁ h p s; exact h.trans_le (h₁.2.1 i j p s hv)
          intro i; exact ih i (ht.mono fun j h=>h.2.2 i) (fun p=>hh (Sum.inr ⟨i,p⟩)) (fun p=>hy (.inr ⟨i,p⟩)) (hc.2 i) hp



lemma find_layers {t:Tree}[Nonempty t.Inner]{s:L→t.Inner→ℝ}{z:Tree.Envelope L t}{M η:ℝ}{r:L→ℝ}[l.NeBot]
      (hr:Tendsto r l (𝓝[>]0))(ht:∀ᶠ i in l,t.Tapered (r i) 1 (s i) ∧ Tree.Relative M η t (s i) (z i))(hM:0≤M)(hη:0<η): ∃ χ:Filter L,χ.NeBot ∧ χ≤l ∧ ∃ (T:L→ℝ)(a:t.Inner→ℝ), (∑ v,a v)=1 ∧ Tendsto T χ atTop ∧ (∀ v,RateIs χ T (fun i=>s i v) (-a v)) ∧ Regular χ T t 0 a z ∧ t.ordered 0 a :=by
      have h₁(v):= sizes_tend (t:=t) hr (ht.mono fun _ hi=>hi.1) le_rfl v
      obtain ⟨χ,hχ,h',T,hT,a,ha,h₂⟩:= clock_compact h₁
      have he: ∀ᶠ i in χ, Tapered t 1 1 (s i) := (ht.and (tendsto_nhds_of_tendsto_nhdsWithin hr |>.eventually_le_const (one_pos: (0:ℝ)<1))|>.mono (fun i ⟨hx,hi⟩=> Tapered.mono hx.1 (by exact le_rfl) (by exact hi))).filter_mono hχ
      have hc:=clock_caps (k:=0) hT (r:=fun _=>1) he h₂ (by simpa only [neg_zero] using RateIs.const (c:=1) hT one_pos)
      exact ⟨χ,h',hχ,T,a,ha,hT,h₂,clock_bound hT ((ht.mono fun i h=>h.2).filter_mono hχ) h₂ (fun v=>tendsto_nhds_of_tendsto_nhdsWithin ((h₁ v).mono_left hχ)) hM hη hc le_rfl,hc⟩
end YM.OPE.Nesting.Tree
