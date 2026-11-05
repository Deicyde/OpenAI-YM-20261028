import YM.MultipleContact.Pair.Puncture
import YM.MultipleContact.TotalRemainder

/-! The exact-order pair extension in a physical puncture patch (normal variable E4, center at e.point 0). Bilateral tests via integration; no assumption of Wightman products on a diagonal. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MultipleContact.Two
open Function Set Filter MeasureTheory Metric Table Power Direct Extraction Spec TopologicalSpace
open scoped Topology BigOperators ContDiff Filter Classical Distributions

section Rules
variable {G:Gauge}{L:Register G}{S:Table L}{P:DiffPlan S} (B:Splitting P)(D:∀k,Detector S k) (Y:Target L→E4→ℂ)

def absoluteTerm (s:ℝ)(m:Option ℕ)(Z:Target L→ E4→ℂ)(f:E4→ℂ)(t:Target L):ℂ:= ∫ x:E4, diff s m f x • Z t x

/-- Equation `ocT` pair rule without an additional patch collar (test and cutoff sufficiently local). -/
def plainRule (s:ℝ) (σ:ℕ)(t:Target L)(f:E4→ℂ):ℂ:=
    if 4≤σ then absoluteTerm s none (miss D (σ-4) Y) f t + ∑i:Fin (σ-4+1), absoluteTerm s (some (σ-4-i)) (piece B D Y (σ-4) i.val) f t
    else absoluteTerm s none Y f t
private lemma factrank : Module.finrank ℝ E4=4:=by simp [E4]
private lemma primaryEquals {R s:ℝ}{f:E4→ℂ} (t:Target L) (hs:0<s)(hr:2*s≤R)(hf:tsupport f⊆ball 0 R)(m:Option ℕ) (Z:Target L→E4→ℂ):
     primary R s m Z f t=absoluteTerm s m Z f t:= by
     unfold primary term absoluteTerm
     refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=> ?_)
     have hfx:f x=0:=by_contra fun h₀=>hx (hf (subset_tsupport _ h₀))
     have hcut:cutoff s x=0:=cutoff_eq_zero hs (hr.trans (le_of_not_gt (fun hi=>hx (mem_ball.mpr ((dist_zero_right ..).le.trans_lt hi))))) -- le eq .trans_lt? equality
     change diff s m f x • Z t x =0
     by_cases m=none
     case pos h=>subst m; exact Eq.trans (congr_arg (fun v:ℂ=>v • Z t x) hfx) (zero_smul ..)
     case neg h=>cases m with
                 | none=>contradiction
                 | some m=> simp [diff,hcut,hfx]
lemma same_rule {σ:ℕ}{R s:ℝ}{f:E4→ℂ} (t:Target L)(hs:0<s)(hr:2*s≤R)(hf:tsupport f⊆ball 0 R): rule B D R s σ Y t f=plainRule B D Y s σ t f:=by
     unfold rule plainRule
     rcases le_or_gt 4 σ with hi|hi
     · let F(k:ℕ):=primary R s none (miss D k Y) f t + ∑i:Fin (k+1),primary R s (some (k-i.val)) (piece B D Y k i.val) f t
       rw [if_pos (factrank.le.trans hi),if_pos hi]
       change F (critical σ E4)=_
       rw [critical,factrank]; unfold F
       simp only [primaryEquals t hs hr hf]
     · simp only [factrank,show ¬ (4 ≤ σ) from not_le_of_gt hi,↓reduceIte]; exact primaryEquals t hs hr hf _ _
end Rules
section Public
variable {G:Gauge}{C:Family G}{S:Table C.book}{P:DiffPlan S} {F:Order}
variable (H:Data C F S P)(A B:S.Tag)(Q:Splitting P)(D:∀k,Detector S k)

set_option quotPrecheck false
lemma dim4 : 1 ≤ Module.finrank ℝ E4:=by rw [factrank]; exact (by decide : (1:ℕ) ≤ 4)
variable {r:ℝ}{N:ℕ}{T:Set (Target C.book)} (he:Estimates P D (massDeg A B) N r (measurePair A B) T) (h₀ : massDeg A B-4 ≤N)
include he h₀ in
lemma valid_patch {U:Opens E4}{t:Target C.book} (ht:t∈T){s:ℝ} (hs:0<s):∃ X:𝓓(U,ℂ) →L[ℂ] ℂ, (∀f:𝓓(U,ℂ),X f=rule Q D r s (massDeg A B) (measurePair A B) t f) ∧ ∀f:𝓓(U,ℂ), tsupport f⊆ball 0 r \ {0} → X f=∫ y:E4, f y * measurePair A B t y:=by
    have h': critical (massDeg A B) E4≤N:=by unfold critical; rw [factrank]; omega
    exact ⟨Power.patch (B:=Q) he dim4 hs h' t ht U,fun _=> patch_on ..,fun f h=>extend_eq (B:=Q) he dim4 hs h' t ht U f (fun hc=>(h hc).2 rfl) (h.trans sdiff_subset)⟩

include he h₀ in
lemma controls_pair : (∀ε:ℝ,0 < ε → Rate (-(massDeg A B:ℝ)-ε) (1+massDeg A B) T (fun s=>rule Q D r s (massDeg A B) (measurePair A B))) ∧
 (∀h:ℕ,h≤N → ∃ γ:ℝ,0<γ ∧ Rate (h-(massDeg A B:ℝ)+γ) (1+massDeg A B) T (fun s t f=>extMiss Q D r s (massDeg A B) h (measurePair A B) t f)) ∧
 (∀h:ℕ,h≤N → ∀w≤h,∃γ:ℝ,0<γ ∧ ReadRate w (1+massDeg A B) ((w:ℝ)-1-(massDeg A B:ℝ)+γ) (fun s f=>Q.part w h (readExtended Q D r s (massDeg A B) h (measurePair A B) f))):=by
 have h':critical (massDeg A B) E4≤N:=by unfold critical; rw [factrank]; omega
 exact ⟨fun ε hv=> normal (B:=Q) dim4 he h' hv,fun h hh=>remainderPrice (B:=Q) he dim4 hh h',fun h hh w hw=>readEstimate (B:=Q) he dim4 hh h' w hw⟩

include H in
lemma e_pair {ι:Type*}[Fintype ι](U:ι → Profile C.book)(hc:Eligible U)(N:ℕ)(hn:massDeg A B-4≤N):∃r> (0:ℝ),
   (∀ V:Opens E4, ∀t∈targets S (includeIndexes D N U),∀s:ℝ, 0<s → ∃X:𝓓(V,ℂ) →L[ℂ] ℂ, (∀f:𝓓(V,ℂ),X f=rule Q D r s (massDeg A B) (measurePair A B) t f) ∧
       ∀f:𝓓(V,ℂ), tsupport f⊆ball 0 r \ {0} → X f=∫ y:E4, f y * measurePair A B t y) ∧
       (∀ε:ℝ,0 < ε → Rate (-(massDeg A B:ℝ)-ε) (1+massDeg A B) (targets S (includeIndexes D N U)) (fun s=>rule Q D r s (massDeg A B) (measurePair A B))) ∧
       (∀h:ℕ,h≤N → ∃ γ:ℝ,0<γ ∧ Rate (h-(massDeg A B:ℝ)+γ) (1+massDeg A B) (targets S (includeIndexes D N U)) (fun s t f=>extMiss Q D r s (massDeg A B) h (measurePair A B) t f)) ∧
       (∀h:ℕ,h≤N → ∀w:ℕ, w≤h → ∃γ:ℝ,0<γ ∧ ReadRate w (1+massDeg A B) ((w:ℝ)-1-(massDeg A B:ℝ)+γ) (fun s f=>Q.part w h (readExtended Q D r s (massDeg A B) h (measurePair A B) f))):=by
     obtain ⟨r,hr⟩:=estimate_batch H A B D Q U N hc
     exact ⟨r,hr.radius_pos,fun V t ht s=> valid_patch A B Q D hr hn ht,controls_pair A B Q D hr hn⟩
end Public
end YM.MultipleContact.Two
