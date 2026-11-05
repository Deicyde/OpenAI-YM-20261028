import YM.OPE.Trees.Combination
/-!
# Rate costs within a single plateau class of a tree

Strictly larger-rate classes may start after some child-scale thresholds and
will carry all gains; for now also need uniform prices on the lowest class
if its rate is ZERO (root's true scale still goes to zero).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset Prescription
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} (U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives} {I J K:Type}[Fintype I][Fintype J]{s:Arboreal I}{i j k:I} {a b:Finset I}{φ:Filter K}[φ.NeBot]{x:K→I→E4}{R:K→I→ℝ}{t:I→ℝ}{M δ ε :ℝ}
    (v:I→ C.book.Token)(ξ:Mode U.sector.derivatives){Y:K→J→ E4}(q:J→ C.book.Token)(L:K→ Viewers U)
local notation "T!"=> (fun i=>s.fullLife (R i))
variable (h:s.Coterie φ t M δ x R)(hp:P.Coherent)(H:Services C F S)
    (hf:Kept φ (fun k=>s.fullLife (R k)) (t i) (fun j=>crop (x j) b))(hg:enveloped φ (fun k=>s.fullLife (R k)) (t i) (fun j=>crop (x j) b) (fun j=> x j i))(hz:i∈ s.zones)
    (hh:Backdrop φ (fun i=>x i s.root) Y)(ht:s.Active a)

local notation "hurry" => (fun i=> spectator U (L i))
include h H
lemma feel_zero (hp:Kept φ T! 0 (fun j=>crop (x j) b))(hb:Backdrop φ (fun i=> x i s.root) Y): RateLE φ T! (fun j=> whole (spectator U (L j)) b (x j) v (Y j) q) 0:=
    (viewer_cost U H.schedule (crop v b) q h.time L hp (hb.life h s.root).1 (hb.around h b) le_rfl le_rfl).mono (by simp)
lemma inserted_cost (hb:Backdrop φ (fun i=> x i s.root) Y)(i:I) : RateLE φ T! (fun j=> pickOne P (spectator U (L j)) (x j) i ξ (Y j) q) 0:=
    (viewer_cost U H.schedule (sole (P.letter ξ)) q h.time L (Kept.sole φ T! _ 0) (hb.life h i).1 (hb.life h i).2 le_rfl le_rfl).mono (by simp)
omit H in
lemma wrapDetector_t {e:ℝ} (ht:Kept φ T! e (fun j=>crop (x j) b))(i:I) : (fun j=> coalesce P b (x j) v i ξ) =ᶠ[φ] fun j=>∑ u∈ (P.sheet ξ).support, (P.sheet ξ) u * whole S b (x j) v (register u (x j i)) u.letter :=by
    filter_upwards [(eventually_all_finset (P.sheet ξ).support).2 (fun u hu=>(Backdrop.child h u i).registered h i ht)] with j hi; unfold coalesce ope; exact sum_congr rfl fun u hu=> congr_arg _ (record_raw u S U.room.kernel (crop v b) (hi u hu))
lemma wrapDetector (a : Finset I)(ht:s.Active a) : (fun j=> coalesce P (s.live a) (x j) v s.root ξ) =ᶠ[φ] fun j=>∑ u∈ (P.sheet ξ).support, (P.sheet ξ) u * whole S (s.live a) (x j) v (register u (x j s.root)) u.letter := wrapDetector_t U v ξ h (h.eternity ht (Subset.refl ..)) s.root
-- no H needed

include hp hf hz hg
lemma fit_coeff : RateLE φ T! (fun j=> coalesce P b (x j) v i ξ) (((OPE.sigma (crop v b):ℝ)-(ξ.1:ℝ))* t i):= by
    cases eq_or_lt_of_le (h.tracked.bounds i hz).1 with
    | inl he=>
       rw [← he,mul_zero]; have he':= wrapDetector_t (P:=P) U v ξ h hf i; refine RateLE.congr (RateLE.sum h.time ?_) he'.symm; intro u hu
       let V(j:K):= x j i; have hx:= feel_zero U v u.letter (fun _=>none) h H (he.symm ▸ hf) (Backdrop.child h u i)
       apply (((RateLE.const ((P.sheet ξ) u) h.time).mul hx)).mono (by rw [zero_add])
    | inr he=> exact available_cost U P _ h.time H hp hg hf he ξ -- order
include hh
lemma fit_remainder (n:ℕ) : RateLE φ T! (fun j=> flux P (spectator U (L j)) b (x j) v i (Y j) q n) ((OPE.sigma (crop v b):ℝ)*t i - (n+1:ℝ)*t i):=by
    cases eq_or_lt_of_le (h.tracked.bounds i hz).1 with
    | inl he=>
       rw [← he,mul_zero,mul_zero,sub_zero]; simp_rw [flow_eq]; refine RateLE.sub (feel_zero U v q L h H (he.symm ▸ hf) hh) (RateLE.sum h.time ?_) h.time; intro j hj;
       apply ((fit_coeff U v j h hp H hf hg hz).mul (inserted_cost U j q L h H hh i)).mono; rw [← he,mul_zero,zero_add]
    | inr he=>
       obtain ⟨m,f,D,hL⟩:= H.purchase; obtain ⟨Z,R,Y,W,hR⟩:= H.along
       exact (group_remainder U (crop v b) q hR h.time H.simpleGate hL H.schedule hp hg hf he L (hh.life h i).2 (hh.life h i).1 le_rfl he le_rfl n).mono (by simp)
omit hf hh hz hg
include ht
lemma Nest.local_room (f:I→Mode U.sector.derivatives) : RateLE φ T! (fun j=> ensemble P s a (x j) v f) (s.onset t v (s.live a) - (f s.root).1*t s.root - ∑ i∈ s.middle a, (f i).1*s.stepAt t i):=by
    rw [← balance P ht f v t]; apply RateLE.prod h.time ?_; intro i hi; exact fit_coeff U (audition P a v f) (f i) h hp H (h.children i) (h.roomy (ht.included hi) (fun _ hv=> Anc.child hv)) (ht.included hi)
lemma Nest.pace (D:I→ℕ) : RateLE φ T! (fun j=>factorization P s a (x j) v ξ D) (s.onset t v (s.live a) - ξ.1*t s.root):=by
    refine RateLE.sum h.time ?_; intro f hf; have he: f s.root=ξ:= ((s.casts ..).1 hf s.root).2 (notMem_erase _ _)
    apply (local_room U v h hp H ht f).mono; rw [he]; exact sub_le_self _ (sum_nonneg (fun u hu=> mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (h.tracked.grows _ (ht.included (mem_erase.mp hu).2)))))
end YM.OPE.Arboreal
