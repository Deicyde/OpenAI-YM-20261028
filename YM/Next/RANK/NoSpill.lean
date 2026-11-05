import YM.Cells.Corrected
import YM.Next.RANK.Alarm
import YM.Next.RANK.Bird


/-!
# Prices that can actually be paid after L (B old -> q)

``Fades`` much smaller than a fixed p margin, not a promise that these costs pay
beta powers. This distinction matters when costs are hit over a trajectory and even
between sqrt(w) and w thresholds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Paint
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

-- costs at real s
abbrev Fades (f : ℝ → ℝ) := ∀ x : ℝ, ∀ᶠ s in atTop, |f s| ≤ bill x s
lemma absorb (a b : ℝ) (h : a < b) (c) : ∀ᶠ s in atTop,c*bill a s≤bill b s:= by
  have he:= bill_hi (a:=a-b) (by linarith); have ht := he.const_mul c; rw [mul_zero] at ht
  filter_upwards [ht.eventually (ge_mem_nhds zero_lt_one)] with s hs
  change c*bill _ _ ≤1 at hs
  have hq := mul_le_mul_of_nonneg_right hs (show 0 ≤ bill b s from Real.exp_pos _|>.le)
  rwa [mul_assoc,overlap, sub_add_cancel,one_mul] at hq
lemma fad_add {f g : ℝ→ℝ} (h : Fades f) (H : Fades g) : Fades fun x=> f x+g x := by
  intro x; filter_upwards [h (x-1),H (x-1),absorb (x-1) x (by linarith) 2] with z hv hf hz
  apply (abs_add_le ..).trans ((add_le_add hv hf).trans _); linarith only [hz]
lemma fad_pay {f g : ℝ→ℝ} (h : Fades f) {a : ℝ} (hg : ∀ᶠ s in atTop, |g s| ≤ bill a s): Fades fun x=>g x*f x := by
  intro b; filter_upwards [h (b-a),hg] with s hs hp
  rw [abs_mul]; apply (mul_le_mul hp hs (abs_nonneg _) (Real.exp_pos _).le).trans; rw [overlap,add_sub_cancel]
lemma either {f : ℝ→ℝ} (h : Fades f) (C : ℝ) : Fades fun x=> C*f x := fad_pay h (a:=1) ((bill_lo (a:=1) zero_lt_one).eventually_ge_atTop |C|)
lemma fad_le {f g : ℝ→ℝ} (h : Fades g) (hf : ∀ᶠ s in atTop, |f s|≤|g s|) : Fades f:= by intro s;filter_upwards [h s,hf] with x h g using g.trans h

-- jolts. old s thresholds

def regular (s : ℝ):= Hat s * bill 1 s


def phase (s : ℝ) := Hat s * hot s
lemma logged (s : ℝ) (he : 0<s) : Hat s= Real.exp (-(Real.log s)/2):= by
  rw [show -(Real.log s)/2 = -(Real.log s/2) by ring, ← Real.log_sqrt he.le,Real.exp_neg,Real.exp_log (Real.sqrt_pos.mpr he)]; rfl
lemma regulog (s : ℝ) (he : 0<s): regular s=Real.exp (-(Real.log s)/2+boil s):=by unfold regular; rw [logged s he,bill,mul_one, ← Real.exp_add]
lemma monitors (A : ℝ) (a : ℝ) (ha : 0 < a) : ∀ᶠ s in atTop,A*boil s ≤ a*Real.log s:= by
  filter_upwards [(Vac.Numbers.monitor A).eventually (ge_mem_nhds ha), eventually_gt_atTop (1:ℝ)] with s hp hs using (div_le_iff₀ (Real.log_pos hs)).mp hp
lemma cooling : Fades Hat := by
  intro x; filter_upwards [monitors (-x) (1/2) (by norm_num),eventually_gt_atTop (0:ℝ)] with s hp h
  rw [logged _ h,abs_of_pos (Real.exp_pos _)]; unfold bill; apply Real.exp_le_exp.mpr; linarith only [hp]
lemma tooCool : Fades regular := by
  rw [show regular=fun s=> bill 1 s*Hat s from funext fun i=> mul_comm ..]
  exact fad_pay cooling (a:=1) (Eventually.of_forall fun s=> (abs_of_pos (show 0<bill 1 s from Real.exp_pos _)).le)

-- vacuum loops unweighted b
lemma faded_three (j : ℕ) (h : 3 ≤ j) : Fades (fun s : ℝ=> s*(regular s)^j):= by
  have hf := fad_pay cooling (a:=3) (show ∀ᶠ s in atTop,|bill 1 s^ (3:ℕ)| ≤ bill 3 s from Eventually.of_forall fun s=> by rw [abs_of_pos (pow_pos (show 0<bill 1 s from Real.exp_pos _) _)] ; unfold bill; rw [← Real.exp_nat_mul]; push_cast; apply le_of_eq; congr 1; ring)
  apply fad_le hf; filter_upwards [eventually_gt_atTop (0:ℝ),tooCool 0] with s hp hs
  have hx : 0 < regular s:= by rw [regulog _ hp]; positivity
  have ha : 0<Hat s:= by rw [logged _ hp]; positivity
  have ht : regular s ≤ 1:= by simpa only [abs_of_pos hx,bill,mul_zero,Real.exp_zero] using hs
  have he : s* Hat s^2=1 := by unfold Hat; rw [inv_pow, Real.sq_sqrt hp.le,mul_inv_cancel₀ hp.ne']
  calc
    _ = s*regular s^j := abs_of_pos (by positivity)
    _ ≤ s*regular s^ (3:ℕ) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx.le ht h) hp.le
    _ = _ := by
      rw [abs_of_pos (mul_pos (pow_pos (show 0<bill 1 s from Real.exp_pos _) _) ha)]; unfold regular; rw [show s*(Hat s*bill 1 s)^3=(bill 1 s)^3*(Hat s)*(s*Hat s^2) by ring,he,mul_one]

lemma timeLoan (b : ℝ) (hb : 1 ≤ b) : Fades fun s=> Hat s ^ b:= by
  apply fad_le cooling; filter_upwards [eventually_gt_atTop (1:ℝ)] with s hp
  have h : Real.log s> 0:= Real.log_pos hp
  rw [logged s (zero_lt_one.trans hp)]
  rw [abs_of_pos (Real.exp_pos _),abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _)]
  nth_rw 2 [← Real.rpow_one (Real.exp _)]
  exact Real.rpow_le_rpow_of_exponent_ge (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith)) hb

lemma dipping (a : ℝ) (h : 0<a) : ∀ᶠ s in atTop, a*(walls s:ℝ) ≥ Real.log s:= by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (a⁻¹),Real.tendsto_log_atTop.eventually_ge_atTop 1] with s hx hs
  have he := Nat.le_ceil ((Real.log s)^2)
  have hp : 1 ≤ Real.log s*a := (inv_mul_cancel₀ h.ne').symm.le.trans (mul_le_mul_of_nonneg_right hx h.le)
  change _ ≤ (M s:ℝ) at he
  have ht : (1:ℝ) ≤ (M s:ℝ) := le_trans (one_le_pow₀ hs) he
  have hy:= pow_le_pow_left₀ (show 0 ≤ Real.log s^2 from sq_nonneg _) he 2
  unfold walls; push_cast; have hb := one_le_pow₀ hs (n:=2); nlinarith

lemma tail_fades (c : ℝ) (h : 0<c) : Fades (fun s=> s * Real.exp (-c*(walls s:ℝ))) := by
  intro x; filter_upwards [monitors (-x) 1 zero_lt_one,dipping (c/2) (by positivity),eventually_gt_atTop (0:ℝ)] with s hx hs hp
  rw [abs_of_pos (mul_pos hp (Real.exp_pos _))]
  nth_rw 1 [← Real.exp_log hp]; unfold bill; rw [← Real.exp_add,Real.exp_le_exp]; linarith only [hx,hs]

lemma wind_pay : ∀ᶠ s in atTop,|wilt (walls s)| ≤ bill 1 s:= by
  let C:= ∑' i,welter i; have h : 0≤C:=tsum_nonneg fun i=> by unfold welter; positivity
  filter_upwards [rate_wall (a:=1/2) (by norm_num) 4,big.eventually_ge_atTop 1,
    absorb (1/2) 1 (by norm_num) (33^4*C)] with s hp hv hs
  have ht : (1:ℝ)≤walls s:= by exact_mod_cast hv
  rw [abs_of_nonneg (wilty _)]
  have he : (↑(walls s):ℝ)^4 ≤ bill (1/2) s := by nth_rw 1 [← Real.exp_log (zero_lt_one.trans_le ht)];rw [← Real.exp_nat_mul]; unfold bill; apply Real.exp_le_exp.mpr; push_cast; linarith
  unfold wilt; apply le_trans _ hs; have hc:= mul_le_mul_of_nonneg_right he h; change (33*_)^4*C≤33^4*C*_;linarith only [hc]

lemma q_power (k : ℕ) (a : ℝ) (ha : 0<a) : ∀ᶠ s in atTop,(↑(walls s):ℝ)^k ≤ bill a s:= by
  filter_upwards [rate_wall ha k,big.eventually_ge_atTop 1] with s hp hv
  have he : 0 < (↑(walls s):ℝ):= by exact_mod_cast hv
  nth_rw 1 [← Real.exp_log he]; rw [← Real.exp_nat_mul]; unfold bill; apply Real.exp_le_exp.mpr; linarith only [hp]
end YM.Next.Rank.Paint
