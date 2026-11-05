import YM.Contacts.Harvest.Yield
/-!
# Passing a test and its budget down to children

Thresholds independent of any inner (dyad) precision. Adjust for the current parent scale even if
subtraction length is much larger. Current masks, directions and proof of sufficient derivative
order with given loss per vertex. Applies to entire stage derivatives. No part of the test cost is
raised to pay another derivative at a distant shell.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest
open Function Filter Set Metric MeasureTheory Submodule Normal
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {E W I : Type} {k : ℕ}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {g l : Normal.Group k}{Q : Pieces g}{P:E→ₗᵢ[ℝ] Points k}
local notation "GN" => Normal.Group k

/-- conditioning of one arm's tests. -/
abbrev tailPay {d : Fin k→ℕ}{l : Normal.Group k}(v : Way d l)(x : ℝ): ℝ:= v.elim (1:ℝ) (fun w=> vanishFactor (levels d l-1-w.val) x)
lemma tailPay_pos {d : Fin k→ℕ}{l : Normal.Group k}(v : Way d l){x : ℝ}(hx:0<x): 0< tailPay v x:= by cases v; exact zero_lt_one; exact vanish_pos _ hx
/-- sufficient global incoming derivative resource. after one persons refinement lose only own
branch test fee depending on dimensions and horizons. -/
def stairs (d : Fin k→ℕ) (Q : Pieces g) := (2+(∑ i,d i))*(g.card-Q.parts.card)
lemma transitions {d : Fin k→ℕ} (i : Q.parts)(v : Splittings i.val) : stairs d (replace i v.val)+levels d i.val+1 ≤ stairs d Q := by
   let t:= (replace i v.val).parts.card; have ht: t≤ g.card:= (replace i v.val).card_parts_le_card; have h:= replace_finer i v.property
   let c : ℕ:= ∑ i,d i; have he:i.val.sum d ≤ c:= Finset.sum_le_sum_of_subset (Finset.subset_univ _)
   have hh : levels d i.val ≤ c+1:= by unfold levels; omega; -- no comparison i.card
   unfold stairs; let q:=Q.parts.card; have h' : q<t:=h
   calc
      _ ≤ (2+c)* (g.card-t)+ (2+c):=by change (2+c)*(g.card-t)+levels d i.val+1 ≤ _; omega -- orientation may need dsimp
      _ = (2+c)* ( (g.card-t)+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (show (g.card-t)+1 ≤ g.card-q from by omega)

namespace Route
variable (r : Route P Q I W)(i : Q.parts) {d : Fin k→ℕ} (b : Way d i.val)
variable (u : Fans P i.val) (v : Splittings i.val) (h : 1 < i.val.card)
local notation "K!" => normalOn P i.val
-- route & fans first as they fix geometry from parent; branch using same length

def net (w : W) := testPlan P d i.val b (r.length w)
def target (w : W)(x : SmoothTests E)(a : ℝ) := mask (u.ray v a) (r.net i b w x)
variable {w : W} {x : SmoothTests E}
lemma haloed (hx : tsupport x.val ⊆ r.stage w) : tsupport (r.net i b w x).val ⊆ halo (normalOn P i.val) (r.length w) (outward b) (r.stage w):= by cases b; exact hx; exact test_halo _ _ (r.short w).1 _ _ hx
lemma halo_small (hx : tsupport x.val ⊆ r.stage w) : tsupport (r.net i b w x).val ⊆ strip (normalOn P i.val) 1 := fun _ h=> le_trans (r.fitted i w (outward b) (r.haloed i b hx h)) r.allows.2
lemma targets {a : ℝ}(ha : 0<a)(hx : tsupport x.val ⊆ r.stage w): tsupport (r.target i b u v w x a).val⊆ r.site i (outward b) u v w a:= fun _ h=> ⟨r.haloed i b hx (support_mask _ _ h).2, u.ray_in v ha (support_mask _ _ h).1⟩
lemma no_target {a : ℝ}(ha : 0<a)(hx : tsupport x.val ⊆ r.stage w)(h : ¬ (r.site i (outward b) u v w a).Nonempty): r.target i b u v w x a=0:= by
   apply Subtype.ext; funext y; exact notMem_support.mp (fun he=> h ⟨y,r.targets i b u v ha hx (subset_closure he)⟩)

private def unitSet := closedBall (0:E) (2+r.reserve) ∩ sun (normalOn P i.val) 1


omit [FiniteDimensional ℝ E] in
private lemma limits_at {t : ℝ}{A : E≃L[ℝ] E}(x:SmoothTests E)(hs : tsupport x.val ⊆ limited A t) : tsupport (composed A x).val ⊆ closedBall (0:E) t:= by
   apply (support_comp (⇑A) A.continuous x.val).trans; intro y hy; rw [mem_closedBall,dist_zero_right]; have he:= limit_iff.mp (hs hy); rwa [A.symm_apply_apply] at he
private lemma normal_sun {K : Submodule ℝ E}{t:ℝ}{A : E≃L[ℝ] E}(h : Proper A t K)(hp : 0<t) : A ⁻¹' sun K t ⊆ sun K 1:= fun x hx=> by
   have he:= (pinch_shell K hp).mpr hx; rw [pinch_normalizes K h hp] at he; exact (pinch_shell _ zero_lt_one).mp he
include h
private lemma restore (w : r.ramp i (outward b) u v)(f:SmoothTests E) (ht: tsupport f.val ⊆ r.site i (outward b) u v w.val.1 w.val.2) : tsupport
   (composed (relaunch (normalOn P i.val) (r.frame w.val.1) w.val.2 (r.R i.val w.val.1) w.property.1.1 (r.valid ..).1) f).val ⊆ r.unitSet i := by
   let R':=r.renew i (outward b) u v h; let A:= R'.frame w; have hw : Proper A w.val.2 K!:= launched _ (r.scaling_frame i w.val.1) w.property.1.1 (r.valid ..).1
   apply subset_inter (limits_at (A:=A) _ (ht.trans (R'.limited_stage w))); refine (support_comp (⇑A) A.continuous f.val).trans (le_trans (Set.preimage_mono (ht.trans (r.sun_shade ..|>.trans inter_subset_left))) (normal_sun hw w.property.1.1)) -- dot args? include h
omit h
private def credit := max (2*r.reserve) r.last
private lemma covers_last : r.last ≤ r.credit:= le_max_right ..
private lemma covers_budget : r.tagalong ≤ r.credit := le_trans r.spends_to (covers_last ..)
private lemma covers_scale : 2*r.reserve ≤ r.credit:= le_max_left ..
private lemma covers_one : 1 ≤ r.credit:= le_trans r.leading (covers_budget ..)
variable {c : ℝ}
include h
private lemma tests_coord (n : ℕ) : ∃ A ≥(1:ℝ),∀ (w : r.ramp i (outward b) u v) (x:SmoothTests E){c:ℝ},
   tsupport x.val ⊆ r.stage w.val.1 → Jet (n+levels d i.val+1) univ (composed (r.frame w.val.1) x).val c →
     Jet n (r.unitSet i) (composed ((r.renew i (outward b) u v h).frame w) (r.net i b w.val.1 x)).val (A*c*tailPay b (w.val.2/r.R i.val w.val.1)):= by
   let L':= levels d i.val; let T:=r.unitSet i; let H : IsCompact T:=(isCompact_closedBall ..).inter_right (closed_sun ..); let N:=n+L'+1; let B:=r.credit
   have ht : T ⊆ sun K! 1:= inter_subset_right; have hB:1≤B:= r.covers_one
   have hp (w) : ∀ a≤ B,∀ x:E,x∈ limited (r.frame w) a → x ∈ limited (r.frame w) B:= fun a ha x ht=> limited_mono ha ht
   cases b with
   | none=>
      obtain ⟨c,hc,h⟩:= from_compact (normalOn P i.val) T H B (zero_le_one.trans hB) L' n
      refine ⟨c,hc,fun q x K hx he=>?_⟩ -- use implicit?
      rw [show tailPay (d:=d) (l:=i.val) none _=1 from rfl,mul_one]; apply h.active he
      have hs:=r.active i u v _ _ q.property.2; have hq:0< r.R i.val q.val.1 := (r.valid ..).1; exact ⟨(div_pos q.property.1.1 hq).le,(div_le_iff₀ hq).mpr (le_trans hs (mul_le_mul_of_nonneg_right (covers_scale r) hq.le))⟩
   | some x =>
      let m:= levels d i.val-1-x.val; obtain ⟨c,hc,he⟩:=compact_deviation (normalOn P i.val) n m H ht B hB
      refine ⟨c,hc, fun w f a hf hp=>?_⟩
      have hs:=r.stay_pay i (outward (d:=d) (i:=i.val) (some x)) h u v w.val.1 w.val.2 w.property.2; let t:=w.val.2 / r.R i.val w.val.1; have hP:0< r.R i.val w.val.1:= (r.valid ..).1
      have hm: m ≤ levels d i.val:= by omega
      apply he t (div_pos w.property.1.1 hP) f (r.scaling_frame i w.val.1) hP (r.short _).1 _ _ _ (hp.weaker (by omega))
      · unfold t; rw [mul_div_cancel₀ _ hP.ne']; exact (div_le_iff₀ (r.short _).1).mpr (hs.trans (mul_le_mul_of_nonneg_right (covers_last r) (r.short _).1.le))
      · exact le_trans (r.in_budget _ i.val i.property h) (mul_le_mul_of_nonneg_right (r.covers_budget) (r.short _).1.le)
      apply (limits_at (A:=r.frame _) f (hf.trans (r.limited_stage _))).trans; intro x hx; change ‖(normalOn P i.val).starProjection x‖ ≤ B/2; rw [mem_closedBall,dist_zero_right] at hx; linarith only [hx, projected_bounded (normalOn P i.val) x, r.covers_scale]

lemma sufficient : ∃ C≥(1:ℝ),∀ (w : r.ramp i (outward b) u v)(x : SmoothTests E) {c:ℝ}, tsupport x.val ⊆ r.stage w.val.1 →
     Jet (stairs d Q) univ (composed (r.frame w.val.1) x).val c → Jet (stairs d (replace i v.val)) univ
       (composed ((r.renew i (outward b) u v h).frame w) (r.target i b u v w.val.1 x w.val.2)).val (C*c*tailPay b (w.val.2 / r.R i.val w.val.1)):= by
    let q:=replace i v.val; let R':=r.renew i (outward b) u v h; let j:= stairs d q
    obtain ⟨C,hc,hA⟩:=r.tests_coord i b u v h j
    let T:=r.unitSet i; let H : IsCompact T:= (isCompact_closedBall ..).inter_right (closed_sun ..)
    obtain ⟨k,hk,hF⟩:= controls (infSmooth (u.ray v 1)) H j
    refine ⟨(2:ℝ)^j*k*C,one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hk) hc,fun w x K hx h'=>?_⟩
    let t:= r.target i b u v w.val.1 x w.val.2; let hp := hA w x hx (h'.weaker (transitions i v)); let B:= R'.frame w
    have he:= hF.times hp (infSmooth _) (infSmooth (composed B (r.net i b w.val.1 x))); apply Jet.recover (U:=T) ?_ (r.restore i b u v h w _ (r.targets i b u v w.property.1.1 hx)) -- shadows `h`
    have hs:(composed B t).val = (u.ray v 1).val * (composed B (r.net i b w.val.1 x)).val:= by rw [← u.ray_proper (A:=B) (launched _ (r.scaling_frame i w.val.1) w.property.1.1 (r.valid ..).1) w.property.1.1 v]; rfl
    change Jet _ _ (composed B t).val _; rw [hs]; exact he.mono (le_of_eq (by ring))
end Route
end YM.Contacts.Harvest

