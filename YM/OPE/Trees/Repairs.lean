import YM.OPE.Trees.Regime
/-!
# Engineering sizes across a tree

The powers of q in the Nest bounds are those of the weights directly summed
among leaf demands. With losses ε each, all charge at once against `fullLife`.
Undoing normalizations at the end here uses *exponential rates*, no lattice
account remains in the continuum telescoping.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Finset Filter
open scoped Classical Topology ContDiff BigOperators
variable {I J : Type}[Fintype I]{a b:Finset I} (s:Arboreal I) (t:I→ℝ) (x:I→E4) {φ:Filter J}{R:J→I→ℝ}{X:J→I→E4}
    {G:Gauge}{L:Register G}(p:I→ L.Token)

lemma sigma_set (a:Finset I) : OPE.sigma (crop p a)=∑ i∈ a,(p i).1:= sum_coe_sort a (fun i=> (p i).1)

/-- Exponential rate spent by undoing all leaf normalizations. -/
def onset (b:Finset I): ℝ:=∑ i∈ b, ((p i).1:ℝ)* t (s.parent i)
/-- Required price engineering factors and ratio factors (unredacted tree).
ε can be 0 here in this expression, though not in the subpower estimate. -/
def tariff (s:Arboreal I)(p:I→ L.Token)(d ε:ℝ)(r:I→ℝ): ℝ:= (r s.root) ^ (d- (OPE.sigma (crop p s.leaves):ℝ)-ε) *
      ∏ u∈ s.middle s.zones,(s.ratioAt r u) ^ (-(OPE.sigma (crop p (s.inputs s.zones u)):ℝ) - ε)
/-- Remainder price. -/
def grace (s:Arboreal I)(r:I→ ℝ) (D:I→ℕ) : ℝ:= ∑ u∈ s.middle s.zones,(s.ratioAt r u)^(D u+1)

lemma appearances (h:s.Active a) : s.onset t p (s.live a) =
      (OPE.sigma (crop p (s.live a)):ℝ) * t s.root + ∑ u ∈ s.middle a,(OPE.sigma (crop p (s.inputs a u)):ℝ)* s.stepAt t u:=by
    let g : I→ℝ:= fun i=>(p i).1; let B:= s.live a
    have he(u j : I)(hp:u∈ s.middle a) (hj:j∈ s.live a): u∈ s.leg a (s.parent j) ↔ j∈ s.inputs a u:=by
       rw [s.leg_in]; exact ⟨fun hv=> mem_filter.mpr ⟨hj,hv.2.joins (Anc.step ..)⟩, fun hv=>⟨hp,inside h (mem_erase.mp hp).2 hv⟩⟩
    simp_rw [sigma_set p,Nat.cast_sum,sum_mul]
    unfold onset; have hq : (∑ u∈ s.middle a, ∑ i∈ s.inputs a u, g i*s.stepAt t u)=∑ i∈ B, ∑ u∈ s.leg a (s.parent i),g i*s.stepAt t u:= by
       apply Finset.sum_comm' (f:=fun u i=> g i*s.stepAt t u); intro u i; constructor
       · rintro ⟨hu,hi⟩; exact ⟨(he u i hu (halfSpace hi)).2 hi,halfSpace hi⟩
       rintro ⟨hk,hv⟩; have hV: u∈ s.middle a:= (s.leg_in .. |>.mp hk).1; exact ⟨hV,(he u i hV hv).1 hk⟩ --- reversed?
    change (∑ i∈ B,g i*_) = (∑ i∈B,g i*_)+_; rw [show (∑ j∈ s.middle a, ∑ i∈ s.inputs a j, ((p i).1:ℝ)*s.stepAt t j)=_ from hq, ← sum_add_distrib]; refine sum_congr rfl fun i hi=>?_ ; rw [← mul_sum, ← mul_add]; congr 1; rw [add_comm (t _), s.level_sum] -- he final
    exacts [h,(s.live_iff ..|>.mp hi).2] -- implicit s.level_sum?

variable {t} {M δ:ℝ} (hc:s.Coterie φ t M δ X R) -- M δ
local notation "T!"=> (fun i=>s.fullLife (R i))
include hc
lemma tariff_life (d ε:ℝ) : RateIs φ T! (fun i=>s.tariff p d ε (R i))
      (s.onset t p s.leaves - d*t s.root + ε):=by
    let E: RateIs φ T! (fun i=> _) _ := (hc.tracked.rates s.root s.initial).rpow (d - (OPE.sigma (crop p s.leaves):ℝ)-ε); -- let sort
    let f (u:I):ℝ:= (OPE.sigma (crop p (s.inputs s.zones u)):ℝ); let t0:= t s.root; let K:= s.middle s.zones
    have hh : ∀ u∈ K, RateIs φ T! (fun i=> (s.ratioAt (R i) u)^(-f u-ε)) ((-f u-ε)*(-s.stepAt t u)):= fun u hu=> (ratio_rate hc.tracked (mem_erase.mp hu).2).rpow _
    apply (E.mul (RateIs.prod hh hc.time)).swap; unfold leaves; rw [s.appearances t p (Action s)];
    have he : (∑ i∈ K, (-f i-ε)*(-s.stepAt t i))=(∑ i∈ K,f i*s.stepAt t i) + ε*(∑ i∈ K,s.stepAt t i):= by rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun _ _=> by ring
    rw [he]; have hp: ∑ i∈ K,s.stepAt t i = 1 - t s.root:= eq_sub_of_add_eq hc.tracked.entire; rw [hp]; unfold f K; ring
-- flat layers (per log comparison)
omit hc
variable {s p}

def SingleLayer (s:Arboreal I)(t:I→ℝ)(a:Finset I)(i:I):=∀ j∈a,s.Anc i j → t j=t i
variable {i j:I}
lemma SingleLayer.condition (h:s.SingleLayer t a i) (h':s.Active a)(he:i∈a)(hp:j∈s.inputs a i): t (s.parent j)=t i := h _ (s.live_iff ..|>.mp (halfSpace hp)).2 (inside h' he hp)
--- i vars
variable (p)
lemma local_charge (h:s.SingleLayer t a i)(h':s.Active a)(hi:i∈a): s.onset t p (s.inputs a i)=(OPE.sigma (crop p (s.inputs a i)):ℝ)*t i :=by
    rw [sigma_set p, Nat.cast_sum,sum_mul]; exact sum_congr rfl fun j hj=> by rw [h.condition h' hi hj]

lemma after_edit (h:s.SingleLayer t a i) (h':s.Active a)(hi:i∈ s.middle a)(y:L.Token) :
    s.onset t (update p i y) (s.live (s.redact a i)) + (OPE.sigma (crop p (s.inputs a i)):ℝ) * t i - (y.1:ℝ) * t i = s.onset t p (s.live a) - y.1 * s.stepAt t i := by
    rw [← local_charge p h h' (mem_erase.mp hi).2]; unfold onset; conv_rhs=> arg 1; arg 1; rw [← s.divide a i]
    rw [pruned h' hi,sum_union (s.divided ..),sum_insert (no_shadow s i a),Function.update_self]
    have he: ∑ x∈ s.external a i, (((update p i y) x).1:ℝ)* t (s.parent x)= ∑ x∈ s.external a i,((p x).1:ℝ)*t (s.parent x):= sum_congr rfl fun j hj=>by rw [Function.update_of_ne (live_other (mem_erase.mp hi).2 (exterior_mem.mp hj).1)]
    rw [he]; unfold stepAt; ring
end YM.OPE.Arboreal
