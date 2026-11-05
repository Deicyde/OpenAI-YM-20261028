import YM.WilsonBulk.Solve.Appetite

/-!
# Actual solution of the unmarked recurrence theorem, absolute part.
  Genuine infinite-depth now at all stipulated levels above ℓ; cone-agnostic.
  Morphology tilt before block. Use full μ/κ. Need not assert pole contribution from e=0;
  done by ObserverRank. Pressure too (before reset).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet.Shop
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {G : Gauge} {A : Levels G} {H : Horizon A} {ℓ i k n N N' e E : ℕ} {x C θ δ : ℝ} {p q r : ℝ→ℝ}
variable {U : Shop H} {B : ℝ}
def waterBill (G : Gauge) (e n E : ℕ) (x : ℝ) := (1+x*x)*levy G E e n x+hopPrice e n x+x
lemma water_tag (G : Gauge) (e n E) : Tariff (waterBill G e n E) := ((((Tariff.const 1 zero_le_one).add (Tariff.one.prod Tariff.one)).prod (levy_formula ..)).add (hops_tag ..)).add Tariff.one
lemma water_le (G : Gauge) (e n E) (h : 0≤x) : x ≤ waterBill G e n E x := le_add_of_nonneg_left (add_nonneg (mul_nonneg (by positivity) ((levy_formula G E e n).1 x h)) ((hops_tag e n).1 x h))
-- no extra Step charge sizes, fill monotone on cone ages. include Pressure footprint by bounding `cDeep*Lullaby`.
lemma uniform_main (hG : G.Simple) (hp : Tariff p) (h : PriorGoods U p e (n+1)) (he : 0< e) (hE : e ≤ U.E) (hf : 1≤n) (hn : n ≤ e+1) :
    ∃ (q : ℝ→ℝ), Tariff q ∧ U.Mono U.main 0 e (n+1) q := by
  let γ:= refill U p; have hz : Tariff γ:= refillCost U _ hp; let Q x:= waterBill G e n U.E (γ x); have hQ : Tariff Q:= (water_tag ..).composed hz
  obtain ⟨S,hS⟩:= lullaby Q hQ U.a (U.bah.trans U.has); refine ⟨S,hS.bill,fun ℓ k x P i N hm hi=>?_⟩
  let Y:=age A.S k x; change i≤N at hi; induction hi using Nat.decreasingInduction with
  | self=>
     let W:= (P.tarmac N (N+1) hm (by omega)).warm; unfold Mora; rw [U.atop N]; exact (W.top e hE _ (by omega)).mono W.era.output_small (((refilled hp _ (P.wisdom N)).trans (water_le G e n U.E (P.conscious N hz))).trans (hS.above _ (P.wisdom N))) -- applications
  | of_succ i hi ih =>
     let s := U.rDeep i; let r:= U.cDeep i n; let xV:= γ (Y i); have hX: 0≤xV:= P.conscious i hz
     have hV : 0≤ S (Y (i+1)):= P.conscious (i+1) hS.bill
     have hh:= P.Levied hp h hm hi hG he hE hf hn (le_refl (γ (Y i))) (ih (by omega))
     have hy := P.Welled hp h hm hi he (le_refl (γ (Y i))) hh
     have ht:= P.large _ hm n hf (by omega)
     have hw : s≤1+xV*xV:= ((P.tarmac i N hm hi).more (refilled hp _ (P.wisdom i))).reflectPrice
     refine hy.mono le_rfl ?_
     apply le_trans ?_ (hS.replenish A.S k x i P.roof)
     change s*(r*S (Y (i+1))+levy G U.E e n xV) + hopPrice e n xV ≤ _
     unfold Q waterBill
     -- exact linear receipt height bars
     linarith only [mul_le_mul_of_nonneg_right ht hV, mul_le_mul_of_nonneg_right hw ((levy_formula G U.E e n).1 xV hX),hX]

lemma uniform_raw (hG : G.Simple) (hp : Tariff p) (h : PriorGoods U p e (n+1)) (he : 0<e) (hE : e≤U.E) (hf : 1≤n) (hn : n ≤ e+1)
    (hs : U.Mono U.main 0 e (n+1) q) (hw : Tariff q) : ∃ r,Tariff r ∧ U.Mono U.raw 1 e (n+1) r := by
  let γ:= refill U p; have hz: Tariff γ:= refillCost U _ hp; let Q:=refill U q; have hQ: Tariff Q:= refillCost U _ hw
  refine ⟨_,hQ.add ((levy_formula G U.E e n).composed hz), fun ℓ k x P i N hm hN=>?_⟩
  let Y:= age A.S k x; have hx : i<N:= hN; have h': U.Mora U.main (i+1) N e (n+1) (Q (Y i)):= (hs ℓ k x P (i+1) N (by omega) hN).mono le_rfl (P.refill_neighbor hw hm)
  exact (P.Levied hp h hm hx hG he hE hf hn (le_refl (γ (Y i))) h').mono le_rfl (add_le_add_left (mul_le_of_le_one_left h'.1 (P.cDeep_small hm hf (by omega))) _) -- syntax left/right
end Parapet.Shop
end YM.WilsonBulk
