import YM.RemainderComparison.Beacon.Terms
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Oils

/-!
 # p^{geo} interface used for the Taylor estimates.
 Call for every stipulated order per step; strengthening the delay or proving
 payment AT the physical scale is a separate theorem; these filters are not
 those powers in m with a *changing* order or L. But backward spend on any
 one stage allocated eta (Reserve.burn) is uniform across all its geometry
 demands and volume. Strict polynomial in fine monitor (includes every
 bolt but not conversely). Path widths/post constants fixed first.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison
open Filter Function Lattice RG Pressure Next.Scheduling Push.AbsoluteSums ConnectedActivityE6
open Coat PhysicalNext.Repeat Lantern
open scoped Topology BigOperators Classical

variable {G : Gauge} {L : Side} {p q : ℝ → ℝ} {t : ℝ}
local notation "M" => Delay.fineMonitor G L
local notation "Z" => (fun x=>betaF G x L)
local notation "U" => Sienna.eaves G L

def Reserve (G : Gauge) (L : Side) (p : ℝ→ℝ) : Prop := ∃ k : ℕ, ∀ᶠ x in atTop,
    |p x| ≤ (Delay.fineMonitor G L x)^k
namespace Reserve

lemma monitoring : Reserve G L M:=
    ⟨1, Eventually.of_forall fun x=> by rw [pow_one,abs_of_pos (Delay.monitor_pos G L x)]⟩
lemma covers (hp : Bolt G L p) : Reserve G L p := ⟨1, by
  simpa only [pow_one,Real.rpow_one] using hp.listens zero_lt_one⟩
lemma const (c : ℝ) : Reserve G L (fun _=> c):= covers (Bolt.still c)
lemma compare (hp : Reserve G L p) (h : ∀ᶠ x in atTop, |q x| ≤ |p x|) : Reserve G L q := by
  obtain ⟨m,hm⟩ := hp; refine ⟨m,?_⟩; filter_upwards [h,hm] with x hx ht using hx.trans ht
lemma rate (h : Reserve G L p) : Rate G L 0 p := by
  obtain ⟨k,h⟩:= h
  have ht := (Rate.monitor (G:=G) (L:=L)).pow k; rw [zero_mul] at ht
  exact ht.compare (h.mono fun x hx=> hx.trans (le_abs_self _))
lemma mul (hp : Reserve G L p) (hq : Reserve G L q) : Reserve G L fun x=> p x*q x:= by
  obtain ⟨i,hi⟩:= hp; obtain ⟨j,hj⟩:= hq; refine ⟨i+j,?_⟩
  filter_upwards [hi,hj] with x hx hy; rw [abs_mul,pow_add]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
lemma pow (hp : Reserve G L p) (n : ℕ) : Reserve G L fun x=> p x^n := by
  induction n with
  | zero => simp only [pow_zero]; exact Reserve.const _
  | succ n ih => simp only [pow_succ]; exact ih.mul hp
lemma add (hp : Reserve G L p) (hq : Reserve G L q) : Reserve G L fun x=> p x + q x:= by
  obtain ⟨i,hi⟩:= hp; obtain ⟨j,hj⟩:= hq
  have hm: Reserve G L (fun x=> 2*((M x)^max i j)) := Reserve.mul (Reserve.const _) (monitoring.pow _)
  refine hm.compare ?_; filter_upwards [hi,hj] with x hx hy
  have hp : 1 ≤ M x:= Real.one_le_exp (sq_nonneg _)
  rw [two_mul]; exact (abs_add_le ..).trans ((add_le_add (hx.trans (pow_le_pow_right₀ hp (le_max_left ..))) (hy.trans (pow_le_pow_right₀ hp (le_max_right ..)))).trans (le_abs_self _))
lemma absolute (hp : Reserve G L p) : Reserve G L (fun x=> |p x|):=
    hp.compare (by simp)
lemma sum (n : ℕ) (f : ℕ → ℝ → ℝ) (hf : ∀ i < n, Reserve G L (f i)) :
    Reserve G L (fun x=> ∑ i∈Finset.range n, f i x) := by
  induction n with
  | zero => simpa using! Reserve.const (G:=G) (L:=L) 0
  | succ n ih => simp_rw [Finset.sum_range_succ]; exact (ih (fun i _=> hf i (by omega))).add (hf n (by omega))
lemma comp (j : ℕ) (hp : Reserve G L p) (hq : Reserve G L q) : Reserve G L fun x=> Lantern.clump j (p x) (q x) :=
  (Reserve.mul (Reserve.const _) hq).mul (((Reserve.const _).add (((Reserve.const _).add hp).mul (Reserve.const _))).pow j)
lemma wig (d : ℝ) : Reserve G L (Sienna.wick G L d) := Reserve.mul (Reserve.const _) monitoring

end Reserve
namespace Access
-- Keep Lane and chart radius on same βhat; permits EXACT β if in it.
local notation "I" => inBand

def apron (G : Gauge) (L : Side) (t : ℝ) := 4*gStep (betaF G t L)
lemma lane_pos {β x:ℝ} (hx : 0<x) (hβ : I x β) : 0<β := by
  have ht : x/4 ≤ β:= hβ.1; linarith

lemma rates_apron : Rate G L (-(1/2)) (apron G L) := by
  let f x:=2*gStep (Z x)
  exact ((Sienna.glim G L).mul_left 2).congr (Eventually.of_forall fun x=> by unfold apron; ring)

lemma wide (h : Rate G L 0 p) :
    ∀ᶠ x in atTop, let u:=Sienna.eaves G L x; let A:=apron G L x
      (0<A ∧ A<u ∧ u<1 ∧ A * |p x| < u) ∧ ∀ β, I (Z x) β → 0 < gStep β ∧ gStep β < A := by
  have hp := rates_apron (G:=G) (L:=L)
  have he := hp.mul (Brim.absolut h); rw [add_zero] at he
  have hg : -(1/2:ℝ) < Sienna.vow:= by norm_num [Sienna.vow]
  filter_upwards [Sienna.contraction (G:=G) L (a:=1) (b:=1) zero_lt_one hp hg, Sienna.contraction G L (a:=1) (b:=1) zero_lt_one he hg, Sienna.below' G L (Sienna.edge G L) Sienna.vow_ok zero_lt_one, Delay.shift_pos G L] with t ht hv ht' hz u A
  have h₀ : 0<gStep (Z t):=(Fare.gS _ hz).1
  refine ⟨⟨show 0<A from mul_pos (by norm_num) h₀,by simpa only [one_mul] using! ht,ht', by simpa only [one_mul] using! hv⟩,fun β hβ=> ?_⟩
  exact ⟨(Fare.gS _ (lane_pos hz hβ)).1, (show gStep β ≤ 2*gStep (Z t) from (band_gap _ β hz hβ).2).trans_lt (show 2*_ < 4*gStep (betaF G t L) from by linarith only [h₀])⟩
lemma exchange (v : ℝ) (k : ℕ) (h : v < -(k:ℝ)/2) (hf : Rate G L v p) :
    ∀ᶠ x in atTop, ∀ β, I (Z x) β → |p x| ≤ (gStep β)^k := by
  have ht : Rate G L ((1/2:ℝ)*k) (fun t=> ((2*Real.sqrt (Z t))^k)):= ((Rate.congr (Rate.power (G:=G) (L:=L) (a:=1/2)) (Eventually.of_forall fun x=> Real.sqrt_eq_rpow _)).mul_left 2).pow _
  filter_upwards [Delay.shift_pos G L, (hf.mul ht).below (by linarith) 1 zero_lt_one] with x hx hh β hb
  have hv : 0 < 2*Real.sqrt (Z x):= mul_pos (by norm_num) (Real.sqrt_pos.mpr hx)
  have hp : (2*Real.sqrt (Z x))⁻¹ ≤ gStep β:=by simpa only [mul_inv_rev,div_eq_mul_inv] using! (show (Real.sqrt (Z x))⁻¹ / 2 ≤ gStep β from (band_gap (Z x) β hx hb).1)
  apply le_trans _ (pow_le_pow_left₀ (inv_pos.mpr hv).le hp k)
  rw [inv_pow, ← one_div, le_div_iff₀ (pow_pos hv _)]
  simpa only [abs_mul, abs_of_pos (pow_pos hv k)] using hh
lemma burn {ε : ℝ} (hε : 0<ε) (hp : Rate G L 0 p) :
    ∀ᶠ x in atTop, ∀ β, I (Z x) β → |p x| ≤ gStep β ^ (-ε) := by
  let u t:=2*gStep (Z t)
  have ht : Rate G L (-(1/2)*ε) (fun t=> (u t)^ε):= by
    intro s hs; let v:= s/ε
    have he : -(1/2:ℝ) < v := (lt_div_iff₀ hε).2 hs
    filter_upwards [Sienna.glim G L v he, Delay.shift_pos G L] with x hx hX
    have hf : 0 < u x:= mul_pos (by norm_num) (Fare.gS _ hX).1
    rw [abs_of_pos (Real.rpow_pos_of_pos hf _)]
    exact (Real.rpow_le_rpow hf.le ((le_abs_self _).trans hx) hε.le).trans_eq (show (Z x ^ v)^ε = _ from (by rw [← Real.rpow_mul hX.le, show v*ε=s from div_mul_cancel₀ s hε.ne']))
  filter_upwards [Delay.shift_pos G L,(hp.mul ht).below (by linarith) 1 zero_lt_one] with x hx hy β hβ
  have hf : 0 < u x:= mul_pos (by norm_num) (Fare.gS _ hx).1
  have he : 0<gStep β:= (Fare.gS _ (lane_pos hx hβ)).1
  apply le_trans _ (Real.rpow_le_rpow_of_nonpos he (show gStep β ≤ u x from (band_gap _ β hx hβ).2) (neg_nonpos.mpr hε.le))
  rw [Real.rpow_neg hf.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hf _)]
  simpa only [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hf ε)] using hy
lemma pay (ε : ℝ) (hε : 0<ε) (hp : Reserve G L p) (k : ℕ) : ∀ᶠ x in atTop, ∀ β, I (Z x) β → (gStep β)^k * |p x| ≤ (gStep β)^((k:ℝ)-ε) := by
  filter_upwards [Delay.shift_pos G L, burn hε hp.rate] with x hx hh β hβ
  have he : 0<gStep β:= (Fare.gS _ (lane_pos hx hβ)).1
  rw [sub_eq_add_neg,Real.rpow_add he,Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left (hh β hβ) (pow_pos he k).le
end Access
end YM.RemainderComparison
