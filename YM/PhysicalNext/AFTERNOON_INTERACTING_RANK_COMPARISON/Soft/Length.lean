import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Yield
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Articles
import YM.Extra.MULTISOURCE_BOUNDS.Merger
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stagecraft
import YM.PhysicalNext.GRADED_QUARTIC_RATE.Stamp
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Fund
import YM.PhysicalNext.SAME_SERVICE_FRESH_DETERMINANT.Orders
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Infinite
import YM.Push.LOOP_COEFFICIENT.ContinuumTrace
import YM.Push.LOOP_COEFFICIENT.Resolution
/-!
# Before paying for the soft stretch, polylogs

ALL these Tends purchased at fixed L after-L. Repeated E transfer
loss may be large at each step. Use explicit growing cost over the
short stretch; not applicable as-is to true vstep continuation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst  Ac Baler Glyph Tapes Marker
open Display Display.Docking  Value Flux SectorNext.Vacuum Station Perch
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

def stretch (L b s : ℝ) : ℕ:= bump L b s + more L s
def advance (s : ℝ) := Real.exp (Perch.y s^3)
def spray (s : ℝ) := s^(-(1/200):ℝ)
def rollup (s : ℝ) (n : ℕ) := spray s * advance s^(4*n)
lemma each_count (s) (k) : rollup s (k+1)=rollup s k*advance s^4:= by
  unfold rollup; rw [Nat.mul_add,Nat.mul_one,pow_add,mul_assoc]

lemma bench_cap (L b : ℝ) (h : 1<L) (hb : 0≤b): ∀ᶠ s in atTop,(stretch L b s:ℝ) ≤ Perch.y s ^4:= by
  let q:=Real.log L; have hq :0<q:=Real.log_pos h
  let C:=(b+2)/q+1+(1/q+1)
  filter_upwards [boil_rate.eventually_ge_atTop 1,many.eventually_ge_atTop 1,rate_wall zero_lt_one 5,boil_rate.eventually_ge_atTop C] with s hs he hy hp
  let f:=boil s;change 1≤ f at hs; have hf: 0≤ f:=boil_pos _
  have ht : Real.log ((YM.Vac.Numbers.P s)^b*(YM.Vac.Numbers.P s)^2)=(b+2)*f:= by unfold YM.Vac.Numbers.P; rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow (Real.exp_pos _),Real.log_pow,Real.log_exp];push_cast;unfold f boil y; ring
  have hM: (bump L b s:ℝ) ≤ (b+2)/q*f+1:= by
    rw [bump,want,ht,div_mul_eq_mul_div]; exact (Nat.ceil_lt_add_one (show 0 ≤ (b+2)*f/q by positivity)).le
  have hP : 1 ≤ (M s:ℝ):= by exact_mod_cast he
  have hv : Real.log ((M s:ℝ)^10) ≤f := by
    unfold walls at hy; rw [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at hy
    rw [Real.log_pow, Nat.cast_ofNat]; linarith only [hy]
  have hx : (more L s:ℝ) ≤ 1/q*f +1:= by
    have hx: 0≤ Real.log ((M s:ℝ)^10):= Real.log_nonneg (one_le_pow₀ hP)
    change (Nat.ceil (_/q):ℝ)≤_
    rw [div_mul_eq_mul_div,one_mul]
    exact (Nat.ceil_lt_add_one (show 0 ≤ Real.log ((M s:ℝ)^10) / q from div_nonneg hx hq.le)).le.trans (add_le_add_left (div_le_div_of_nonneg_right hv hq.le) _)
  unfold stretch; rw [Nat.cast_add]; refine le_trans ?_ ((mul_le_mul_of_nonneg_right (show C ≤ f from hp) hf).trans_eq ?_)
  · unfold C; linarith only [hs,hM,hx]
  unfold f boil; ring

lemma advance_large (C : ℝ): ∀ᶠ s in atTop,bill C s≤ advance s:=by
  filter_upwards [Perch.y_rate.eventually_ge_atTop C] with s hs; apply Real.exp_le_exp.mpr
  change Perch.y s^2*C ≤ Perch.y s^3; calc
    _ ≤ Perch.y s^2*Perch.y s:= mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by ring
lemma advances : Tendsto advance atTop atTop:= Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (n:=3) (by norm_num)).comp Perch.y_rate)
lemma advancement (A : ℝ) (k : ℕ) (hA : 0<A): ∀ᶠ s:ℝ in atTop, Perch.y s ^k ≤ A * Real.log s:= by
  have hx := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k |>.comp Perch.y_rate
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0),hx.eventually (ge_mem_nhds hA)] with s hs hu
  change Perch.y s^k*Real.exp (-Perch.y s) ≤ A at hu
  rw [Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _),Perch.y,Real.exp_log (show 0<Real.log s from hs)] at hu; exact hu
lemma machine (L b : ℝ) (k : ℕ) (h : 1<L) (hb : 0≤b): ∀ᶠ s in atTop, ∀ n≤ stretch L b s,
    rollup s n * advance s^k ≤ s^(-(1/400):ℝ) := by
  let f:ℝ:= 1/(400*(k+4:ℝ)); have hf: 0<f:= by unfold f; positivity
  filter_upwards [bench_cap L b h hb, Perch.y_rate.eventually_ge_atTop 1,advancement f 7 hf, eventually_gt_atTop (0:ℝ)] with s ht he hE hs n hp
  unfold rollup advance spray; rw [Real.rpow_def_of_pos hs, Real.rpow_def_of_pos hs, ← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add]; apply Real.exp_le_exp.mpr
  have hz:(n:ℝ)≤ Perch.y s^4:= (Nat.cast_le.mpr hp).trans ht
  have ht : (n:ℝ)*(Perch.y s)^3 ≤ Perch.y s^7:= (mul_le_mul_of_nonneg_right hz (by have := (show 1≤ Perch.y s from he); positivity)).trans_eq (by ring)
  have hk : Perch.y s^3 ≤ Perch.y s^7 := pow_le_pow_right₀ he (by norm_num)
  have hx:f*(400*(k+4:ℝ))=1:= by unfold f; field_simp
  have hm := mul_le_mul_of_nonneg_left hE (show 0≤ (k+4:ℝ) by positivity); push_cast
  linarith only [hm,mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg k (α:=ℝ)),ht,show f*(400*(k+4:ℝ))*Real.log s=Real.log s by rw [hx,one_mul]]
lemma floor_spray {s:ℝ} (h : 0<s) (hv : 1≤ advance s) (i : ℕ) : spray s≤ rollup s i:= le_mul_of_one_le_right (Real.rpow_pos_of_pos h _).le (one_le_pow₀ hv)
end YM.PhysicalNext.InteractingRank.Soft
