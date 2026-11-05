import YM.AnalyticNext.QUARTIC_MATCH.Radius.Fruit
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Change
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Rove
/-! # Per-post financial thresholds. Widths paid ahead, recurrence through short stretch. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst Pump Ac Baler Glyph Tapes Marker
open Display Display.Docking Display.Sew Value Flux SectorNext.Vacuum Station Perch
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

lemma paid_eff (L : Side) (a t : ℝ) (ht : 0<t): ∀ᶠ s:ℝ in atTop, ∀ x∈Set.Icc (s/2) s,∀ n : ℕ,payment (rollup s n) a t 1 L (walls x) ≤ weather s n := by
  let C:= payment 1 a t 1 L 0
  have hC:0 ≤ C := by
    unfold C payment Push.AbsoluteSums.Footprint.payment Push.AbsoluteSums.Footprint.degreeIncome
    have hp:= Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le); have hy: 0≤1-Real.exp (-t):= sub_nonneg.mpr hp; positivity
  filter_upwards [advance_large 2, Perch.half.eventually_ge_atTop 1,(big.comp Perch.half).eventually_ge_atTop 1,Paint.q_power 4 1 zero_lt_one, (bill_lo zero_lt_one).eventually_ge_atTop (C*43^4)] with s he hp hV hc hQ x hx n
  let W:=walls x; let R:=rollup s n; have hw: W≤walls s:= wall_mono (hp.trans hx.1) (hp.trans (hx.1.trans hx.2)) hx.2
  have h' : (1:ℕ) ≤ W:= le_trans (show 1 ≤ walls (s/2) from hV) (wall_mono hp (hp.trans hx.1) hx.1)
  have ht': 0<s:=zero_lt_one.trans_le (hp.trans (hx.1.trans hx.2))
  have hR:0≤R:= mul_nonneg (Real.rpow_pos_of_pos ht' _).le (pow_nonneg (Real.exp_pos _).le _)
  let f : ℝ:= (21*W+21*W+1:ℕ)^ (4:ℕ)
  have hh : payment R a t 1 L W=C*f*R:=by unfold C f payment Push.AbsoluteSums.Footprint.payment Push.AbsoluteSums.Footprint.degreeIncome Push.AbsoluteSums.Footprint.spread Push.AbsoluteSums.Footprint.extentCost Push.AbsoluteSums.Animals.ballCost; push_cast; ring
  have hl : f ≤ (43:ℝ)^4 * (walls s:ℝ)^4:= by
    rw [← mul_pow]; unfold f; exact_mod_cast Nat.pow_le_pow_left (show 21*W+21*W+1≤43*walls s by omega) 4
  change payment _ _ _ _ _ W ≤ _; rw [hh,mul_comm _ R]; apply mul_le_mul_of_nonneg_left _ hR
  refine ((mul_le_mul_of_nonneg_left hl hC).trans ?_).trans he
  rw [←mul_assoc,show (2:ℝ)=1+1 by norm_num,← Perch.overlap]; exact mul_le_mul hQ hc (by positivity) (Real.exp_pos _).le

lemma risibly {B : ℕ} {d c : ℝ} (h : Risible B d) (ha : 0≤c) (hp : c ≤ d) : Risible B c:= ⟨ha,(mul_le_mul_of_nonneg_left hp (by positivity)).trans h.grain⟩
lemma exp_bound {c : ℝ} (ha : 0≤c) (hp : c≤1) : Real.exp c-1≤ 2*c:=by
  have ht:= Real.abs_exp_sub_one_le (by rw [abs_of_nonneg ha]; exact hp); rw [abs_of_nonneg ha] at ht; exact (le_abs_self _).trans ht
lemma cost_shorten (L : Side) (P Q : BudgetPoint) {e M l d y v c : ℝ} (h : Lease L P Q e M l d y v) (hc : 0<c) (he : c ≤ d) (hp : wilt Q.B*((Fintype.card (Site L):ℝ)*(salary (e+1)*v)) ≤ c): Lease L P Q e M l c y v:= by
  have hC' : 16*c ≤1:= le_trans (mul_le_mul_of_nonneg_left he (by norm_num)) h.enough
  have ht:Real.exp (2*c)-1 ≤4*c:=by linarith only [exp_bound (show 0≤2*c by linarith only [hc]) (show 2*c≤1 by linarith only [hc,hC'])]
  have hu : 1+16*c ≤ Real.exp (16*c):= by rw [add_comm]; exact Real.add_one_le_exp _
  have hd:0<1+16*c:=by linarith only [hc]
  have hz:(1+16*c)⁻¹ ≤ 1-4*c:= by apply le_of_mul_le_mul_left _ hd; rw [mul_inv_cancel₀ hd.ne']; nlinarith only [hc,hC']
  refine { h with
    sparks:=hp, inferno:= risibly h.inferno (by positivity) (mul_le_mul_of_nonneg_left he (by norm_num)), volume:= (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) (by unfold ReLog.roof; positivity)).trans h.volume,enough:=hC',
    small:=?_, patches:=(mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by norm_num)) (mul_nonneg (zero_le_one.trans h.lamps) zero_le_two)).trans h.patches,
    fees:=le_trans (add_le_add_left (sub_le_sub_right (Real.exp_monotone (mul_le_mul_of_nonneg_left he (by norm_num:0≤(2:ℝ)))) _) _) h.fees,
    due:= he.trans h.due, cap:=hc.le }
  rw [Real.exp_neg]; linarith only [ht,(inv_anti₀ hd hu).trans hz]
structure Escalates (ξ : Purse) (L : Side) (s : ℝ) : Prop where
  rate n : n ≤ stretch L.val ξ.band s → rollup s n ≤ 1
  books (n : ℕ) (x y : ℝ) (P Q : BudgetPoint) : n ≤ stretch L.val ξ.band s → x∈Set.Icc (s/2) s → y∈Set.Icc (s/2) s → Q.B=walls x →
    Lease L P Q (load ξ.era) (acres ξ x y) (Line ξ.era ξ.goal 0 s) (tinder ξ s) (kinetics s) (gas ξ.era.coast y) → Lease L P Q (load ξ.era) (acres ξ x y) (Line ξ.era ξ.goal 0 s) (sailboat s n) (kinetics s) (gas ξ.era.coast y)
  reserves (n : ℕ) (x : ℝ) (P : BudgetPoint) : n ≤ stretch L.val ξ.band s → x∈Set.Icc (s/2) s → P.B=walls x →
    Grid.garlic (retime x) ≤ weather s n ∧ 8*weather s n ≤ 1 ∧ Risible P.B (8*weather s n) ∧ Line ξ.era ξ.goal 0 s * (Real.exp (8*weather s n)-1)≤ sailboat s n
  accept (n : ℕ) : spray s+16*sailboat s n ≤ rollup s (n+1)
  marks : 1≤ s
lemma waterfall (ξ : Purse) (hb : 0≤ξ.band) (L : Side) (hl : 1 < (L.val:ℝ)): ∀ᶠ s in atTop, Escalates ξ L s:= by
  let c:ℝ:= 2*ξ.goal+10
  filter_upwards [luxury ξ, machine L.val ξ.band 3 hl hb, pay_sparks ξ L,advances.eventually_ge_atTop 17, risibleQ, garlicPay, long_pay c (1/400) (by norm_num), (bill_hi (by dsimp only [c]; have := Nat.cast_nonneg (α:=ℝ) ξ.goal; linarith : -c<0)).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)), eventually_ge_atTop (1:ℝ), Paint.absorb (-c) (-1/8) (by unfold c; linarith [Nat.cast_nonneg (α:=ℝ) ξ.goal]) 4] with s hL hp he hQ hy hG hs hT h h'
  have h₁ : 0<s:=zero_lt_one.trans_le h
  let v:=advance s; have he' : 1≤ v:= le_trans (by norm_num : (1:ℝ)≤17) hQ
  have ht : (0:ℝ)< spray s:=Real.rpow_pos_of_pos h₁ _
  have hv n : rollup s n ≤ sailboat s n:= le_mul_of_one_le_right (ht.le.trans (floor_spray h₁ he' _)) (one_le_pow₀ he')
  have hM n (hm:n≤ stretch L.val ξ.band s): sailboat s n≤bill (-c) s:= (hp n hm).trans (hs s ⟨half_le_self h₁.le,le_rfl⟩)
  have hx:bill (-c) s≤1:=hT
  refine ⟨fun n hp=> (hv _).trans ((hM n hp).trans hx), fun n x y P Q hn hx hy hB A=> cost_shorten L P Q A (ht.trans_le ((floor_spray h₁ he' _).trans (hv _))) ?_ ?_, fun n x P hn hx hB=>?_,fun n=>next_rate s h₁ hQ n,h⟩
  · convert! hM n hn using 1; unfold tinder c; rw [neg_add]; ring_nf
  · rw [hB]; exact (he x hx y hy).trans ((floor_spray h₁ he' _).trans (hv _))
  let u:=weather s n
  have hh:3*u ≤ 8*u:= by
    have he:0≤u:=mul_nonneg (ht.le.trans (floor_spray h₁ he' _)) (Real.exp_pos _).le
    linarith only [he]
  have hb:0≤u:=by linarith only [hh]
  have ha: v* (16*u)≤ sailboat s n:= by
    have h₂:= mul_le_mul_of_nonneg_left (show 16≤v by linarith only [show 17≤v from hQ]) hb
    have hz:= mul_le_mul_of_nonneg_left h₂ (zero_le_one.trans he'); unfold sailboat; unfold u v weather at *; linarith only [hz]
  have hc : 8*u ≤ (sailboat s n):= le_trans (by linarith only [hb, mul_le_mul_of_nonneg_right he' hb] : 8*u ≤ v*(16*u)) ha
  have hd : sailboat s n ≤1:= (hM n hn).trans (show bill _ _≤ _ from hT)
  have hz : Risible P.B (kinetics s/4):= (hy P x hB hx).2.1
  have hj: sailboat s n≤ kinetics s/4:= by linarith only [show 4*bill (-c) s≤ kinetics s from h',hM n hn]
  exact ⟨(hG x hx).trans ((floor_spray h₁ he' _).trans (le_mul_of_one_le_right (ht.le.trans (floor_spray h₁ he' _)) he')),
    hc.trans hd, risibly hz (mul_nonneg (by norm_num) hb) (hc.trans hj),
    (mul_le_mul_of_nonneg_left ((exp_bound (show 0≤8*u by positivity) (hc.trans hd)).trans (by change 2*(8*u)≤16*u;linarith only)) (zero_le_one.trans (le_max_left 1 _))).trans ((mul_le_mul_of_nonneg_right hL (show 0 ≤ 16*u by positivity)).trans ha)⟩
end YM.PhysicalNext.InteractingRank.Soft
