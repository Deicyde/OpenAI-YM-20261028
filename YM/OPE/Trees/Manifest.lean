import YM.OPE.Trees.Errors
/-!
# Uniform nested estimates, epsilon-version (for every ratio in (0,bar_q])

`sample`: every output, lifetimes of these detectors for the overall and
smaller products, and factorization with explicit horizon-gains.
`session`: raw-horizon result incl unselected and every character, actually
the strength available on the ground discrepancy. These are coupled finite
horizon results; not uniqueness assertions. Combining any finite list of such
requirements over the same tree (& layout) needs just their common tail (thus
can also require e.g. lifetime for all detectors through every band that
participates).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset Prescription
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives} {I J K:Type}[Fintype I][Fintype J]{s:Arboreal I}{a:Finset I}{φ:Filter K}[φ.NeBot]{x:K→I→E4}{R:K→I→ℝ}{t:I→ℝ}{M δ c ε :ℝ}
    (v:I→ C.book.Token)(ξ:Mode U.sector.derivatives) (D:I→ℕ) {Y:K→J→ E4} (q:J→ C.book.Token) (n:ℕ)
local notation "T!"=> (fun i=>s.fullLife (R i))
variable (h:s.Coterie φ t M δ x R)(hp:P.Coherent)(H:Services C F S)
include h hp H
private lemma of_gain (he:0<ε) : ∀ᶠ j in φ, ‖coalesce P s.leaves (x j) v s.root ξ - factorization P s s.zones (x j) v ξ D‖ ≤ s.tariff v ξ.1 ε (R j)*s.grace (R j) D:=by
    by_cases ha:s.middle s.zones=∅
    · unfold leaves; filter_upwards with j; rw [Nest.staging P (x j) ξ s.Action ha]; simp [grace,ha]
    let d(i:I):ℝ:= ((D i+1:ℕ):ℝ)*s.stepAt t i; obtain ⟨i,hi,hν⟩:= (s.middle s.zones).exists_min_image d (nonempty_iff_ne_empty.mpr ha)
    have hx:= error_pace U v ξ h hp H s.Action D (show s.boundAt t D s.zones (d i) from hν); let w:= s.tariff v ξ.1 ε; have hg:= s.tariff_life v h ξ.1 ε
    have hq(k)(he:k∈ s.middle s.zones):RateIs φ T! (fun j=> (s.ratioAt (R j) k)^(D k+1)) (-d k):= ((ratio_rate h.tracked (mem_erase.mp he).2).power (D k+1)).swap (by unfold d; ring)
    filter_upwards [(hg.mul (hq i hi)).outweigh hx (by unfold leaves; linarith only [he]) h.time,hg.pos,(eventually_all_finset (s.middle s.zones)).2 fun i hi=>(hq i hi).pos] with j hj hg hh;
    exact hj.trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun x hx=> (hh x hx).le) hi) hg.le)
omit h hp H

structure Qualified (s:Arboreal I) (P:Prescription U.sector.derivatives)(ξ:Mode U.sector.derivatives)(x:I→E4): Prop where
    outer (u:Exterior C.book): u∈ (P.sheet ξ).support→ Injective (beside (away (crop x s.leaves) (x s.root)) (bearing u))
    step (i:I)(u:Exterior C.book): i∈ s.zones→u∈ (P.sheet ξ).support→ Injective (beside (away (crop x (s.kids i)) (x i)) (bearing u))

-- arg order U or s first test
include h
lemma qualified : ∀ᶠ i in φ,s.Qualified U P ξ (x i) :=by
    filter_upwards [(eventually_all_finset (P.sheet ξ).support).2 fun u hu=> (h.pinned u s.root s.leaves (h.eternity s.Action (Finset.Subset.refl ..))).and (eventually_all.mpr (fun i=>h.pinned u i (s.kids i) (h.children i)))] with i hi; exact ⟨fun u hu=> (hi u hu).1,fun i u _ hu=> (hi u hu).2 i⟩

omit h

structure ValueRate (s:Arboreal I)(P: Prescription U.sector.derivatives)(ξ:Mode U.sector.derivatives)(v:I→ C.book.Token)(D:I→ℕ)(ε:ℝ)(x:I→E4)(r:I→ℝ): Prop where
    lifetimes : s.Qualified U P ξ x
    direct : ‖coalesce P s.leaves x v s.root ξ‖ ≤ s.tariff v ξ.1 ε r
    combination : ‖coalesce P s.leaves x v s.root ξ-factorization P s s.zones x v ξ D‖ ≤ s.tariff v ξ.1 ε r*s.grace r D
structure TestedRate (s:Arboreal I)(P:Prescription U.sector.derivatives)(p:I→ C.book.Token)(q:J→ C.book.Token)(n:ℕ)(ε:ℝ)(x:I→ E4)(r:I→ℝ)(y:J→ E4): Prop where
    right : Injective (beside (crop x s.leaves) y)
    apertures : Injective (beside (sole (x s.root)) y)
    ready : Tested U P n (crop x s.leaves) (crop p s.leaves) (x s.root) y q (s.tariff p ((n:ℝ)+1) ε r)

include H hp
lemma sample (s:Arboreal I)(hm:0≤M)(hd:0<δ)(he:0<ε) : ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→E4)(t:I→ℝ), t s.root=r → s.Convoy M δ t x → s.ValueRate U P ξ v D ε x t:=by
    let P' (r:ℝ)(x:(I→E4)×(I→ℝ)):= x.2 s.root=r ∧ s.Convoy M δ x.2 x.1
    have hh : ∀ᶠ r:ℝ in 𝓝[>]0, ∀ x:(I→E4)×(I→ℝ), P' r x→ s.ValueRate U P ξ v D ε x.1 x.2:= by
       refine refine_geometry ?_; intro f ψ hN hh hf; let y r:=(f r).2; let x r:=(f r).1; have hk: Tendsto (fun i=> y i s.root) ψ (𝓝[>]0):= (tendsto_id.mono_left hh).congr' (hf.mono (fun _ h=>h.1.symm)); obtain ⟨χ,hX,hY,t,hT⟩:= phase_rates (hf.mono (fun i hi=> hi.2.sizes)) hk
       have hx:s.Coterie χ t M δ x y:= ⟨(hf.mono (fun _ h=> h.2)).filter_mono hX,hm,hd,hT,hk.mono_left hX⟩; refine ⟨χ,hY,hX,?_⟩
       filter_upwards [(s.tariff_life v hx ξ.1 ε).outweigh (director_pace U v ξ hx hp H s.Action) (by unfold leaves; linarith only [he]) hx.time,qualified (P:=P) U ξ hx,of_gain U v ξ D hx hp H he] with i hp hf hv using ⟨hf,hp,hv⟩
    filter_upwards [hh] with i h x t hv ht using (h (x,t) ⟨hv,ht⟩)
lemma session (s:Arboreal I)(hm:0≤M)(hd:0<δ)(he:0<ε)(hc:0<c):∀ᶠ r:ℝ in 𝓝[>]0, ∀ (x:I→ E4)(t:I→ℝ)(y:J→E4), t s.root=r → s.Convoy M δ t x → ClearOf (x s.root) y c → s.TestedRate U P v q n ε x t y:=by
    let P'(r:ℝ)(x:(I→E4)×(I→ℝ)×(J→E4)):= x.2.1 s.root=r ∧ s.Convoy M δ x.2.1 x.1 ∧ ClearOf (x.1 s.root) x.2.2 c; have hh : ∀ᶠ r:ℝ in 𝓝[>]0, ∀ x:(I→E4)×(I→ℝ)×(J→E4), P' r x→ s.TestedRate U P v q n ε x.1 x.2.1 x.2.2:= by
       refine refine_geometry ?_; intro f ψ hN hh hf; let y r:=(f r).2.1; let Y r:=(f r).2.2; let x r:=(f r).1; have hk:Tendsto (fun i=>y i s.root) ψ (𝓝[>]0):= (tendsto_id.mono_left hh).congr' (hf.mono fun _ hi=>hi.1.symm); obtain ⟨χ,hX,hY,t,hT⟩:= phase_rates (hf.mono fun _ hi=> hi.2.1.sizes) hk
       have hx:s.Coterie χ t M δ x y:= ⟨(hf.mono fun _ hi=> hi.2.1).filter_mono hX,hm,hd,hT,hk.mono_left hX⟩; have hv:Backdrop χ (fun i=>x i s.root) Y:=⟨c,hc,(hf.mono (fun _ hi=> hi.2.2)).filter_mono hX⟩; refine ⟨χ,hY,hX,?_⟩
       filter_upwards [(s.tariff_life v hx ((n:ℝ)+1) ε).outweigh (factor_ground U v q hx hp H s.Action hv n) (by unfold leaves; linarith only [he]) hx.time,overall_injected hx hv s.Action,root_inject hx hv] with i hi he he' using ⟨he,he', tested U P n _ _ (x i s.root) (Y i) q hi he he'⟩
    filter_upwards [hh] with i h x t y hz he hv using h (x,t,y) ⟨hz,he,hv⟩
end YM.OPE.Arboreal
