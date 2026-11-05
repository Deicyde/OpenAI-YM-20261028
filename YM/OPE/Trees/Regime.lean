import YM.OPE.Trees.Dial
/-!
# Clustering geometries and log-rate regimes of their centers

Require spacing of whole subpatterns: lower bound δ on distance/s between
positions of distinct child groups. Does not matter if a child agrees with
its own root position. Ratios cap only `≤1`, so in particular covers all
sizes in `(0,bar_c]` for sufficiently small `bar_c`. Extent bounded with
all recursive costs through any fixed tree. `Horizons` use also widely
separated centers without any upper test radius demands.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset Real
open scoped Classical ContDiff Topology BigOperators
variable {I J L:Type}[Fintype I][Fintype J]{φ : Filter L}{s:Arboreal I}{a b: Finset I}{t r:I→ℝ}{X:I→E4}
    {p M δ c C:ℝ}{i j k:I}{x:L→I→E4}{R:L→I→ℝ}

structure Convoy (s:Arboreal I)(M δ:ℝ)(r:I→ℝ)(x:I→E4) : Prop where
    sizes : Graduated s r
    travel (i:I): ‖x i-x (s.parent i)‖ ≤ M*r (s.parent i)
    spread (i j k:I): s.Fork i j k → δ*r i ≤ ‖x j-x k‖

lemma Convoy.near {r:I→ℝ}(h:s.Convoy M δ r X)(hm:0≤ M)(hp:s.Anc i j)(hi:i∈ s.zones): ‖X j-X i‖ ≤ (s.depth j:ℝ)* (M*r i):=by
    have he:= (mul_nonneg hm (h.sizes.allowed _ hi).le); refine hp.along (fun j=> ‖X j-X i‖ ≤ (s.depth j:ℝ)*(M*r i)) (by simpa using mul_nonneg (Nat.cast_nonneg (α:=ℝ) (s.depth i)) he) (fun j hk hz hh hx=> ?_)
    have hR:j≠s.root:= fun hv=>hh (hv.trans ((show s.Anc i s.root from hv ▸ hk).excess).symm); have ho : (s.depth (s.parent j):ℝ) + 1 ≤ s.depth j := by exact_mod_cast s.step j hR
    calc _ ≤ ‖X j-X (s.parent j)‖+ ‖X (s.parent j)-X i‖:= c_dist_point ..
         _ ≤ M*r (s.parent j)+(s.depth (s.parent j):ℝ)*(M*r i):= add_le_add (h.travel j) hx
         _ ≤ ((s.depth (s.parent j):ℝ)+1)*(M*r i):=by rw [add_mul,one_mul]; linarith only [mul_le_mul_of_nonneg_left (h.sizes.bound (hk.back hh) (s.inward j)) hm]
         _ ≤ _ := mul_le_mul_of_nonneg_right ho he

abbrev crop {V: Type*}(x:I→V)(b:Finset I) : (↑b:Type) → V :=fun i=>x i.val

local notation "T!"=> (fun i:L=>s.fullLife (R i))

/-- Tracked accounting plus placements. -/
structure Coterie (s:Arboreal I)(φ: Filter L)(t:I→ℝ)(M δ:ℝ)(x:L→I→E4)(R:L→I→ℝ): Prop where
    space : ∀ᶠ k in φ,s.Convoy M δ (R k) (x k)
    cap : 0 ≤ M
    keep : 0 < δ
    tracked : s.Traced φ t R
    collapse : Tendsto (fun i=> R i s.root) φ (𝓝[>] 0)

variable (h:s.Coterie φ t M δ x R)
namespace Coterie
include h

lemma time : Tendsto T! φ atTop:= turning (h.space.mono (fun i hi=>hi.sizes)) h.collapse
-- include h?
lemma pixels (he:i∈s.zones) : Tendsto (fun j=> R j i) φ (𝓝[>] 0):= all_root (h.space.mono (fun i hi=>hi.sizes)) h.collapse he
lemma closes (hi:i∈ s.zones) (he:s.Anc i j) : Tendsto (fun k=>‖x k j-x k i‖) φ (𝓝 0):= by
    apply squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) (h.space.mono (fun k hk=> hk.near h.cap he hi)); simpa using (((tendsto_nhdsWithin_iff.mp (h.pixels hi)).1.const_mul M)|>.const_mul ((s.depth j):ℝ))
lemma roomy (he:i∈ s.zones)(hv:∀ j∈b,s.Anc i j): enveloped φ T! (t i) (fun j=>crop (x j) b) (fun j=> x j i):=by
    have hp(j)(hu:s.Anc i j):RateLE φ T! (fun k=>x k j-x k i) (-t i):= ((((RateLE.const ((s.depth j):ℝ) h.time).mul ((RateLE.const M h.time).mul ((h.tracked.rates i he).pays h.time)))).mono (by simp)).of_norm_le (h.space.mono (fun k h'=> h'.near h.cap hu he))
    intro v hv'; filter_upwards [eventually_all.mpr (fun j:(↑b:Type)=> hp j.val (hv j.val j.property) _ hv')] with k hk using (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr hk
lemma divided_cost (hp:s.Fork i j k)(hr:t i<p) : ∀ᶠ n in φ, Real.exp (-p * s.fullLife (R n)) < ‖x n j-x n k‖:= (((RateIs.const h.time h.keep).mul (h.tracked.rates i hp.inner)).overtakes (RateLE.exp (-p) h.time) h.time (by rw [zero_add]; linarith only [hr])).and h.space|>.mono fun n h=>h.1.trans_le (h.2.spread _ _ _ hp)
lemma eternity (he:s.Active a)(ha:b⊆ s.live a): Kept φ T! 1 (fun i=>crop (x i) b):=by
    intro p hp; refine eventually_all.mpr fun (i:(↑b:Type))=>eventually_all.mpr fun j=>eventually_all.mpr fun hk=> ?_; have hi:i.val≠j.val:= Subtype.val_injective.ne hk; obtain ⟨u,hu,-,hU⟩:= s.divergence (lived he (ha i.property) (ha j.property) hi) (lived he (ha j.property) (ha i.property) hi.symm) (s.closure i.val) (s.closure j.val); exact h.divided_cost hU ((h.tracked.bounds _ hu).2.trans_lt hp)
lemma children (i:I) : Kept φ T! (t i) (fun j=>crop (x j) (s.kids i)):=by
    intro p hp; refine eventually_all.mpr fun (u:(↑(s.kids i):Type))=>eventually_all.mpr fun k=>eventually_all.mpr fun hh=> ?_; exact h.divided_cost (aurora u.property k.property (Subtype.val_injective.ne hh) (Anc.same ..) (Anc.same ..)) hp
lemma resting (he:s.Active a)(hi:i∈s.middle a):Intervals φ T! (t (s.parent i)) (fun j=>sole (x j i)) (fun j=>crop (x j) (s.external a i)):=by
    intro p hp; refine eventually_all.mpr fun u=>eventually_all.mpr fun v=>?_ ; obtain ⟨k,-,hk,hf⟩:=fork_rest he hi v.property; exact h.divided_cost hf ((path_rate h.tracked hk (s.inward i)).trans_lt hp)
lemma contained (he:s.Active a)(hi:i∈a) (hv:∀ j∈a,s.Anc i j → t j ≤ t i) : Kept φ T! (t i) (fun j=>crop (x j) (s.inputs a i)):=by
    intro p hp; refine eventually_all.mpr fun u=>eventually_all.mpr fun v=>eventually_all.mpr fun ht=>?_ ; have hx:=Subtype.val_injective.ne ht; obtain ⟨k,-,hk,hU⟩:= s.divergence (lived he (halfSpace u.property) (halfSpace v.property) hx) (lived he (halfSpace v.property) (halfSpace u.property) hx.symm) (show s.Anc i u.val from (mem_filter.mp u.property).2) (show s.Anc i v.val from (mem_filter.mp v.property).2)
    exact h.divided_cost hU ((hv k (he.ancestral (hU.left.1.back hU.left.2) (s.live_iff ..|>.1 (halfSpace u.property)).2) hk).trans_lt hp)
end Coterie
end YM.OPE.Arboreal
