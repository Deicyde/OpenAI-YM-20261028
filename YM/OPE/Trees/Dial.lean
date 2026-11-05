import YM.OPE.Trees.Line
import YM.OPE.Exchange.Regime
/-!
# Clock for collapsing lengths

No lower gate on scale ratios. To prove the exponent-loss version, compactify
log ratios normalized by their total with the root's running log. A family of
violating configurations would already violate along a refinement on which all
these relative accounts have limits. Equal rates DO NOT mean comparable length
(their ratio can still go to zero). `Traced` will allow both cases.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Finset Filter Real
open scoped Classical Topology BigOperators ContDiff
variable {I L : Type}{s:Arboreal I}{a:Finset I}{i j k:I}
    {φ ψ: Filter L}{T:L→ℝ}{r t:I→ℝ}

structure Graduated (s:Arboreal I) (r:I→ℝ) : Prop where
   allowed (i:I) : i∈ s.zones→ 0 < r i
   coarser (i:I): i∈ s.zones→ r i ≤ r (s.parent i)

variable (s)
def fullLife (r:I→ℝ) := (∑ i∈ s.middle s.zones, s.stepAt (fun i=> run (r i)) i)+run (r s.root)
variable {s}

lemma Graduated.bound (h:s.Graduated r)(he:s.Anc i j)(hv:j∈ s.zones) : r j ≤ r i:=he.along (fun j=> r j ≤ r i) le_rfl (fun j _ hr _ ht=> (h.coarser j (hr.inner hv)).trans ht)
lemma Graduated.life (h:s.Graduated r)(hi:i∈s.zones): 0 ≤ s.stepAt (fun i=>run (r i)) i:=sub_nonneg.mpr (neg_le_neg (log_le_log (h.allowed _ hi) (h.coarser i hi)))
lemma Graduated.limit (h:s.Graduated r)(hi:i∈ s.zones): run (r i) ≤ s.fullLife r:=leg_mono (r:=fun i=>run (r i)) (fun i hi=>h.life (mem_erase.mp hi).2) (Action s) hi
lemma Graduated.rising (h:s.Graduated r)(hi:i∈ s.zones): run (r s.root) ≤ run (r i):=neg_le_neg (log_le_log (h.allowed _ hi) (h.bound (s.closure _) hi))

variable {R:L→ I→ℝ} (h:∀ᶠ j in φ,s.Graduated (R j))(hr:Tendsto (fun i=> R i s.root) φ (𝓝[>] 0))
include h hr
lemma turning : Tendsto (fun i=>s.fullLife (R i)) φ atTop:=by
    refine tendsto_atTop_mono' φ ?_ (run_towards hr); exact h.mono (fun i hi=> hi.limit s.initial)
lemma all_root (hi:i∈s.zones): Tendsto (fun j=> R j i) φ (𝓝[>] 0):=by
    refine tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (h.mono (fun j hj=>(hj.allowed _ hi).le)) (h.mono (fun j hj=> hj.bound (s.closure i) hi)) (tendsto_nhdsWithin_iff.mp hr).1,h.mono (fun j hj=>hj.allowed _ hi)⟩
variable [Fintype I]
structure Traced (s:Arboreal I)(φ:Filter L)(t:I→ℝ)(R:L→I→ℝ) : Prop where
    rates (i:I): i∈s.zones→ RateIs φ (fun i=>s.fullLife (R i)) (fun j=>R j i) (-t i)
    bounds (i:I): i∈s.zones→ 0 ≤ t i ∧ t i ≤1
    grows (i:I): i∈s.zones→ t (s.parent i) ≤ t i
    entire : (∑ i∈ s.middle s.zones,s.stepAt t i)+ t s.root = 1

lemma phase_rates [φ.NeBot] : ∃ ψ : Filter L, ψ ≤ φ ∧ ψ.NeBot ∧ ∃ t:I→ℝ, s.Traced ψ t R:=by
    let T i:= s.fullLife (R i); let f i (j: I):= run (R i j)/T i; let V (i) : (↑(s.zones):Type) → ℝ:= fun j=> f i j
    have hs:=run_towards hr
    have hT: Tendsto T φ atTop:= turning h hr; have hm:= hT.eventually_gt_atTop 0
    have hw: ∀ᶠ i in φ, ∀ j∈ s.zones,0≤ f i j ∧ f i j ≤ 1:=by filter_upwards [hm,h,hs.eventually_gt_atTop 0] with i hi hp hx j hj using ⟨div_nonneg (le_trans hx.le (hp.rising hj)) hi.le,(div_le_one hi).2 (hp.limit hj)⟩
    obtain ⟨ψ,hp,hP,x,hX⟩:=Next.UVStress.finite_extract (𝓛:=φ) V 1 (hw.mono (fun i hi=> (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun y=>by rw [Real.norm_of_nonneg (show 0 ≤ V i y from (hi y.val y.property).1)]; exact (hi y.val y.property).2)); let t (i:I):= if h:i∈s.zones then x ⟨i,h⟩ else 0
    have he i (hi:i∈s.zones): Tendsto (fun j=>f j i) ψ (𝓝 (t i)):=by rw [show t i = x _ from dif_pos hi]; exact tendsto_pi_nhds.mp hX ⟨i,hi⟩
    have hV:= h.filter_mono hp; have hν:= hm.filter_mono hp
    refine ⟨ψ,hp,hP,t,?_⟩; constructor
    · intro i hi; refine ⟨hV.mono (fun j h=> h.allowed _ hi), Tendsto.congr (fun i'=>?_) ((he i hi).neg)⟩; change -(f _ i)=_; unfold f run; rw [neg_div, neg_neg]
    · intro i hi; exact ⟨ge_of_tendsto (he i hi) ((hw.filter_mono hp).mono (fun j h=> (h i hi).1)), le_of_tendsto (he i hi) ((hw.filter_mono hp).mono (fun j h=>(h i hi).2))⟩
    · intro i hi; apply le_of_tendsto_of_tendsto (he (s.parent i) (s.inward i)) (he i hi); -- maybe prime version
      filter_upwards [hV,hν] with i' hi' hx using div_le_div_of_nonneg_right (sub_nonneg.mp (hi'.life hi)) hx.le
    have he': Tendsto (fun i=> (∑ j∈ s.middle s.zones,s.stepAt (f i) j)+f i s.root) ψ (𝓝 ((∑ i∈ s.middle s.zones,s.stepAt t i)+t s.root)):= (tendsto_finsetSum _ (fun i hi=> (he i (mem_erase.mp hi).2).sub (he (s.parent i) (s.inward ..)))).add (he _ s.initial)
    refine tendsto_nhds_unique_of_eventuallyEq he' tendsto_const_nhds ?_
    filter_upwards [hν] with i hi; change (∑ j∈ s.middle s.zones,s.stepAt (f i) j)+f i s.root=1; unfold stepAt f; simp_rw [← sub_div]; rw [← Finset.sum_div, ← add_div]; exact div_self (show T i ≠ 0 from hi.ne')

omit h hr [Fintype I]
lemma path_rate (h:s.Traced φ t R) (he:s.Anc i j)(hj:j∈s.zones): t i ≤ t j:= he.along (fun j=>t i ≤ t j) le_rfl (fun x _ hi _ hx=> hx.trans (h.grows _ (hi.inner hj)))
lemma ratio_rate (h:s.Traced φ t R)(he:i∈ s.zones): RateIs φ (fun i=> s.fullLife (R i)) (fun j=> s.ratioAt (R j) i) (-s.stepAt t i):= ((h.rates i he).div (h.rates _ (s.inward _))).swap (by unfold stepAt; ring)
end YM.OPE.Arboreal
