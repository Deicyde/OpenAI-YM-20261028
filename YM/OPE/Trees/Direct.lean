import YM.OPE.Trees.Prior
/-!
# Direct readouts and same phase discrepancy across multiscale log regimes
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset Prescription
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives} {I J K:Type}[Fintype I][Fintype J]{s:Arboreal I}{i j k:I} {a b:Finset I}{φ:Filter K}[φ.NeBot]{x:K→I→E4}{R:K→I→ℝ}{t:I→ℝ}{M δ c ε d e:ℝ}
    (v:I→ C.book.Token)(ξ:Mode U.sector.derivatives){Y:K→J→ E4}(q:J→ C.book.Token)(L:K→ Viewers U)
local notation "T!"=> (fun i=>s.fullLife (R i))
variable (h:s.Coterie φ t M δ x R)(hp:P.Coherent)(H:Services C F S) (ht:s.Active a)

-- endowment when adding weight, repair-shrink functions. Generic for all fees,
-- in particular for when targeting an error sum or a subpower bound.
include h hp H ht
lemma pays_weight (he:s.Leap t a i) (u:Mode U.sector.derivatives) {f: K→ℂ} (hc:RateLE φ T! f (s.onset t (update v i (P.letter u)) (s.live (s.redact a i)) - d)) : RateLE φ T! (fun j=> coalesce P (s.inputs a i) (x j) v i u*f j) (s.onset t v (s.live a)-d - u.1*s.stepAt t i):=by
    obtain ⟨hs,hy⟩:= layer_geom h ht he.single he.active; have hw:= fit_coeff U v u h hp H hs hy (ht.included he.active); apply (hw.mul hc).mono; have hE:= after_edit v he.single ht he.inner (P.letter u); rw [show (P.letter u).1=u.1 from rfl] at hE; linarith only [hE] -- defeq?
lemma expansion {g:Presentment I K C.book}
    (hr : ∀ (b:Finset I) (hb:s.Active b) (v:I→ C.book.Token),
         (∀ i:I, s.Leap t b i → s.Forever P x b i v φ T! g) ∧ (s.SingleLayer t b s.root → RateLE φ T! (fun j=>g j b v) (s.onset t v (s.live b)-d))) : RateLE φ T! (fun j=>g j a v) (s.onset t v (s.live a)-d):=by
    induction hN:a.card using Nat.strong_induction_on generalizing a v with | h n ih
    by_cases he:s.SingleLayer t a s.root; · exact (hr a ht v).2 he
    obtain ⟨i,hi⟩:= Leap.exists he h ht; let u:=s.onset t v (s.live a)-d; obtain ⟨j,hj⟩:= ((hr a ht v).1 i hi u).exists
    let f(w: Mode U.sector.derivatives)(k:K):=g k (s.redact a i) (update v i (P.letter w)); let w' (w)(k:K):=coalesce P (s.inputs a i) (x k) v i w * f w k
    have hg : RateLE φ T! (fun k:K=>∑ w ∈ bands U.sector.derivatives j,w' w k) u:= by
       refine RateLE.sum h.time ?_; intro w hw; exact (pays_weight U v h hp H ht hi w (ih _ (hN ▸ redact_gains hi.active) _ (redacted ht hi.inner) rfl)).mono (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hi.above.le)) -- order inspect
    apply (hj.add hg h.time).congr; filter_upwards with j; exact sub_add_cancel ..
lemma director_pace : RateLE φ T! (fun j=> coalesce P (s.live a) (x j) v s.root ξ) (s.onset t v (s.live a)-ξ.1*t s.root):= by
    apply expansion U v h hp H ht (g:=fun j b v=> coalesce P (s.live b) (x j) v s.root ξ); intro b h' v; refine ⟨fun i hh=> useful_coeff U v ξ h hp H h' hh,fun hx=>?_⟩; have hw:=layer_geom h h' hx h'.main
    have hk:= local_charge v hx h' h'.main; rw [s.top_roots] at hk hw; rw [hk,← sub_mul]; exact fit_coeff U v ξ h hp H hw.1 hw.2 s.initial
lemma general_flux (he:Backdrop φ (fun j=> x j s.root) Y)(n:ℕ) : RateLE φ T! (fun j=> flux P (spectator U (L j)) (s.live a) (x j) v s.root (Y j) q n) (s.onset t v (s.live a) -(n+1:ℝ)*t s.root):=by
    apply expansion U v h hp H ht (g:=fun j b v=> flux P (spectator U (L j)) (s.live b) (x j) v s.root (Y j) q n); intro b h' v; refine ⟨fun i hh=> useful_flux U v q L h hp H h' hh he n,fun hx=>?_⟩; have hw:=layer_geom h h' hx h'.main; have hk:=local_charge v hx h' h'.main; rw [s.top_roots] at hk hw; rw [hk]; exact fit_remainder U _ q L h hp H hw.1 hw.2 s.initial he n

omit [φ.NeBot] hp H ht in
lemma root_inject (he:Backdrop φ (fun j=> x j s.root) Y) : ∀ᶠ j in φ, Injective (beside (sole (x j s.root)) (Y j)):=by
    obtain ⟨hq,hξ⟩:= he.life h s.root; exact (Kept.sole φ _ _ 0|>.chorus hq hξ)|>.inject
-- remove H etc
lemma factor_ground (he:Backdrop φ (fun j=> x j s.root) Y)(n:ℕ) : RateLE φ T! (fun j=> groundError U P n (crop (x j) (s.live a)) (crop v (s.live a)) (x j s.root) (Y j) q) (s.onset t v (s.live a) -(n+1:ℝ)*t s.root):= by
    apply ground_cost U P n (crop v (s.live a)) q (overall_injected h he ht) (root_inject h he); exact fun ψ=> general_flux U v q ψ h hp H ht he n
end YM.OPE.Arboreal
