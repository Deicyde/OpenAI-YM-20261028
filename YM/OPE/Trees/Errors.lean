import YM.OPE.Trees.Direct
/-!
# Every fixed truncation schedule.

Telescope only when there's gain. If anywhere a ratio *charge* vanishes,
the Nest error sum already covers both bounds. Otherwise every horizon edge
that carries error is power-separated in the relative log regime and can
actually be matched locally to a much higher auxiliary horizon. Drop the
intermediate excess terms, paying the requested factor. No forall-horizon
claim is made for any particular positive fixed r.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset Prescription
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives} {I J K:Type}[Fintype I][Fintype J]{s:Arboreal I}{i j k:I} {a:Finset I}{φ:Filter K}[φ.NeBot]{x:K→I→E4}{R:K→I→ℝ}{t:I→ℝ}{M δ d:ℝ}
    (v:I→ C.book.Token)(ξ:Mode U.sector.derivatives)
local notation "T!"=> (fun i=>s.fullLife (R i))
variable (h:s.Coterie φ t M δ x R)(hp:P.Coherent)(H:Services C F S) (ht:s.Active a)
local notation "Λ"=> U.sector.derivatives

def boundAt (s:Arboreal I)(t:I→ℝ)(D:I→ℕ)(a:Finset I)(d:ℝ):= ∀ i∈ s.middle a,d ≤ ((D i+1:ℕ):ℝ)*s.stepAt t i
include h hp H ht
lemma within_leap (D:I→ℕ)(hl:s.Leap t a i) (hb:s.boundAt t D a d) : RateLE φ T! (s.alter P a v x i (D i) (fun j b v=> coalesce P (s.live b) (x j) v s.root ξ)) (s.onset t v (s.live a)-ξ.1*t s.root-d):=by
    let f(j:K)(b:Finset I)(v:I→C.book.Token):= coalesce P (s.live b) (x j) v s.root ξ; let u:=s.onset t v (s.live a)-ξ.1*t s.root-d; obtain ⟨n,hN,hr⟩:= ((useful_coeff U v ξ h hp H ht hl u).and (eventually_ge_atTop (D i))).exists
    let c (w:Mode Λ)(j:K):= coalesce P (s.inputs a i) (x j) v i w * f j (s.redact a i) (update v i (P.letter w)); let a':= bands Λ (D i); have he:a'⊆ bands Λ n:= fun w hw=>(full_bands ..).2 (((full_bands ..).1 hw).trans hr)
    have hx:RateLE φ T! (fun j=>∑ w∈ bands Λ n \ a',c w j) u:=by
       refine RateLE.sum h.time ?_; intro w hw; have hu: D i<w.1:= lt_of_not_ge (fun hh=>(mem_sdiff.mp hw).2 ((full_bands ..).mpr hh)); apply (pays_weight U v h hp H ht hl w (director_pace U _ ξ h hp H (redacted ht hl.inner))).mono; unfold u; linarith only [hb i hl.inner,(mul_le_mul_of_nonneg_right (show ((D i+1:ℕ):ℝ)≤ (w.1:ℝ) from Nat.cast_le.mpr hu) hl.above.le)]
    refine (hN.add hx h.time).congr ?_; filter_upwards with j; change (f j a v - (∑ w∈ bands Λ n,c w j))+(∑ w∈ bands Λ n \ a',c w j)= f j a v-∑ w∈ a', c w j; rw [sum_sdiff_eq_sub he]; ring

lemma error_pace (D:I→ℕ)(hb:s.boundAt t D a d) : RateLE φ T! (fun j=> coalesce P (s.live a) (x j) v s.root ξ - factorization P s a (x j) v ξ D) (s.onset t v (s.live a)-ξ.1*t s.root-d):=by
    induction hN:a.card using Nat.strong_induction_on generalizing a v with | h n ih
    by_cases hd: d≤ 0
    · exact ((director_pace U v ξ h hp H ht).sub (Nest.pace U v ξ h hp H ht D) h.time).mono (by linarith only [hd]);
    by_cases he : (s.middle a)=∅
    · -- no error when there are no intermediate nodes
      apply RateLE.congr (RateLE.zero φ T! _) (Eventually.of_forall (fun j=>?_)); rw [Nest.staging P (x j) _ ht he D,sub_self];
    obtain ⟨i,hi,hV⟩:= terminals (nonempty_iff_ne_empty.mpr he); let a':= s.redact a i; have he':s.Active a':= redacted ht hi
    have hξ:0 < ((D i+1:ℕ):ℝ):=by positivity
    have hl:s.Leap t a i:= Leap.terminal hi hV (pos_of_mul_pos_right (lt_of_lt_of_le (lt_of_not_ge hd) (hb i hi)) hξ.le)
    let f(w:Mode Λ)(j):= coalesce P (s.live a') (x j) (update v i (P.letter w)) s.root ξ; let g(w:Mode Λ)(j):=factorization P s a' (x j) (update v i (P.letter w)) ξ D; let w' (w:Mode Λ)(j):= coalesce P (s.inputs a i) (x j) v i w
    let μ:= (ξ.1:ℝ)*t s.root; let u:=s.onset t v (s.live a)-μ-d; have hc : RateLE φ T! (fun j=>∑ w∈ bands Λ (D i),w' w j*(f w j-g w j)) u:=by
       refine RateLE.sum h.time ?_; intro w hw; have hf:= ih a'.card (hN ▸ redact_gains hl.active) (update v i (P.letter w)) he' (fun i hi=> hb _ ((erase_subset_erase _ (redacting hl.active)) hi)) rfl; apply (pays_weight U v h hp H ht hl w (d:=μ+d) (RateLE.mono hf (le_of_eq (by dsimp only [μ]; ring)))).mono; dsimp only [u]; linarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) w.1) hl.above.le]
    apply ((within_leap U v ξ h hp H ht D hl hb).add hc h.time).congr; filter_upwards with j;
    rw [Nest.contracted P hV hi]; change coalesce P _ _ _ _ _ - (∑ w∈ bands Λ (D i),w' w j*f w j)+(∑ w∈ bands Λ (D i),w' w j*(_ - _))=coalesce P _ _ _ _ _ - ∑ w∈ bands Λ (D i), w' w j*g w j; simp only [mul_sub,sum_sub_distrib]; ring
end YM.OPE.Arboreal
