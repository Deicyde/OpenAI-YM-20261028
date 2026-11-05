import YM.OPE.Trees.Association
import YM.OPE.Trees.Extel
/-!
# Expansion across different log-relative lengths

At a strict pace elevation, which may at the same time start a number of
single-pace descendant vertices, match this **one active forest** as a
single-radius product at that relative log length, rather than approximating
ratio degenerations by new trees. Here we expand through a high enough *finite*
horizon selected locally, valid with power accuracy which now beats any given
power by taking this horizon large enough **at fixed pace data**. This choice
of stopping horizon WON'T survive in the final Nest estimates. Thanks to
equal-log-rate arities & the power-separated viewer discrepancy, no diagonal
selection of OPE or RG layouts at the current tree is necessary here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset Prescription
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives} {I J K:Type}[Fintype I][Fintype J]{s:Arboreal I}{i j k:I} {a b:Finset I}{φ:Filter K}[φ.NeBot]{x:K→I→E4}{R:K→I→ℝ}{t:I→ℝ}{M δ c C' ε :ℝ}
    (v:I→ C.book.Token)(ξ:Mode U.sector.derivatives){Y:K→ J→ E4}(q:J→ C.book.Token)(L:K→ Viewers U)
local notation "T!"=> (fun i=>s.fullLife (R i))
variable (h:s.Coterie φ t M δ x R)(hp:P.Coherent)(H:Services C F S) (hh:Backdrop φ (fun i=>x i s.root) Y)(ht:s.Active a)

structure Leap (s:Arboreal I)(t:I→ℝ)(a:Finset I)(i:I): Prop where
    inner : i ∈ s.middle a
    above : 0 < s.stepAt t i
    single : s.SingleLayer t a i
lemma Leap.exists (ha: ¬ s.SingleLayer t a s.root)(h:s.Coterie φ t M δ x R)(ht:s.Active a) : ∃ i, s.Leap t a i:=by
    let V:= a.filter fun i=> 0<s.stepAt t i; have hv: V.Nonempty:=by
       by_contra hc; apply ha; intro i hi hA; refine hA.along (fun i=> t i=t s.root) rfl (fun j _ hh hz he=> ?_); have hx:j∈a:= ht.ancestral hh hi; have hk : ¬0 < t j - t (s.parent j):= fun h'=> hc ⟨j, mem_filter.mpr ⟨hx,h'⟩⟩; linarith only [hk,(h.tracked.grows _ (ht.included hx)),he]
    obtain ⟨v,hv,hV⟩:= V.exists_max_image s.depth hv; obtain ⟨h₁,h₂⟩:= (mem_filter.mp hv); have hw:s.stepAt t s.root=0:= by rw [stepAt,s.direct, sub_self]
    refine ⟨v,⟨mem_erase.mpr ⟨fun hr=> lt_irrefl (0:ℝ) ((show 0 < s.stepAt t s.root from hr ▸ h₂).trans_le hw.le),h₁⟩,h₂,(fun j hj hi=>hi.along (fun j=> t j=t v) rfl (fun k hk h𝕜 h₀ hq=> ?_))⟩⟩; have hx:k∈a:=ht.ancestral h𝕜 hj; have hf : ¬0 < t k - t (s.parent k) := fun he=>not_lt_of_ge (hV k (mem_filter.mpr ⟨hx,he⟩)) (hk.into h₀); linarith only [hf,hq,(h.tracked.grows _ (ht.included hx))]
lemma Leap.active (hl:s.Leap t a i): i∈a:= (mem_erase.mp hl.inner).2
lemma Leap.after (hl:s.Leap t a i): t (s.parent i) < t i:= sub_pos.mp hl.above
lemma Leap.terminal (he:i∈s.middle a)(hf:s.Border a i)(h:0<s.stepAt t i) : s.Leap t a i:=⟨he,h, fun k hk hk'=> hf k hk hk' ▸ rfl⟩

variable (he:s.Leap t a i)
include h ht
lemma layer_geom (hz:s.SingleLayer t a i)(hg:i∈a): Kept φ T! (t i) (fun j=> crop (x j) (s.inputs a i)) ∧ enveloped φ T! (t i) (fun j=>crop (x j) (s.inputs a i)) (fun j=>x j i):= ⟨h.contained ht hg (fun i hi h=> (hz i hi h).le),h.roomy (ht.included hg) (fun v hv=>(mem_filter.mp hv).2)⟩
include hh he
lemma priority_beyond : let y (j:K):= beside (crop (x j) (s.external a i)) (Y j); Kept φ T! 1 y ∧ Intervals φ T! (t (s.parent i)) (fun j=>sole (x j i)) y:=by
    have hp:= hh.life h i; intro y; refine ⟨(h.eternity ht (sdiff_subset ..)).chorus (hp.1.mono zero_le_one) ((hh.around h (s.external a i)).mono zero_le_one), ?_⟩
    intro p hx; filter_upwards [h.resting ht he.inner p hx,hp.2 p ((h.tracked.bounds _ (s.inward i)).1.trans_lt hx)] with j h hh k u; rcases u with u|u; exacts [h k u, hh k u]
include hp H
-- Core `superP`, argument order profile. `wrapDetector` extrudes prices.
lemma strict_expands (u:ℝ) : ∀ᶠ n:ℕ in atTop, RateLE φ T! (fun j=>whole (spectator U (L j)) (s.live a) (x j) v (Y j) q-∑ w∈ bands U.sector.derivatives n, coalesce P (s.inputs a i) (x j) v i w * whole (spectator U (L j)) (s.live (s.redact a i)) (x j) (update v i (P.letter w)) (Y j) q) u:=by
    obtain ⟨he',hq⟩:= layer_geom h ht he.single he.active; obtain ⟨h₁,h₂⟩:=priority_beyond h hh ht he; obtain ⟨M,r,D,hP⟩:= H.purchase; obtain ⟨M',V,E,W,hR⟩:= H.along; obtain ⟨hs,hw⟩:= h.tracked.bounds (s.parent i) (s.inward i)
    let y (j):= beside (crop (x j) (s.external a i)) (Y j); let Y':= beside (crop v (s.external a i)) q
    have hE (n:ℕ):= group_remainder (Y:=y) U (crop v (s.inputs a i)) Y' hR h.time H.simpleGate hP H.schedule hp hq he' (lt_of_le_of_lt hs he.after) L h₂ h₁ hw he.after hs n
    let f (n:ℕ):ℝ:= (OPE.sigma (crop v (s.inputs a i)):ℝ)*t i-((n:ℝ)+1)*(t i-t (s.parent i))+(OPE.sigma Y':ℝ)*1; have hN:Tendsto f atTop atBot:=by
       let q:= t i-t (s.parent i); let b:=(OPE.sigma (crop v (s.inputs a i)):ℝ)*t i - q + (OPE.sigma Y':ℝ)*1; have heq:f=fun (n:ℕ)=> b- q*(n:ℝ):= by funext n; unfold f b q; ring
       rw [heq]; apply tendsto_atBot.mpr; intro v; filter_upwards [(tendsto_natCast_atTop_atTop.const_mul_atTop (show 0<q from he.above)).eventually_ge_atTop (b-v)] with i hi; linarith only [hi]
    filter_upwards [hN.eventually_le_atBot u] with n hn; apply RateLE.congr ((hE n).mono hn);
    filter_upwards [overall_injected h hh ht,overall_injected h hh (redacted ht he.inner)] with j hx hy; let V:= spectator U (L j); have hw := (spectate U (L j)).laws.toSymmetric; change whole V (s.inputs a i) (x j) v (y j) Y' - _ = whole V (s.live a) (x j) v (Y j) q - _; refine congrArg₂ (·-·) (logs_combine V hw (s.divide ..) (s.divided ..) hx).symm (sum_congr rfl fun w hz=> ?_); exact congr_arg (coalesce P (s.inputs a i) (x j) v i w * ·) (one_combine V hw P (pruned ht he.inner).symm (no_shadow s i a) hy).symm
end YM.OPE.Arboreal
