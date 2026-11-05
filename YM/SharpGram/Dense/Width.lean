import YM.Pert.Dense.Portal
/-!
# Slim interior windows.

Work AFTER Bar fixed, independently of arbitrary other Wait requirements; final
construction can satisfy both. Keep each stage-j request length at most

`floor(log(hatBeta)/log(L_stage))`.

This bounds lost transmission from the predecessor stage by ONE coupling power
in `hatBeta`, much smaller than what general sublin bounds would give. Need
check it can still carry all the demands in `StationPort.Certified` (dense
Poised supplier). At fixed stage it's larger asymptotically than the
`benchCost` minimum in the physical price accounts: these use powers of
monitor and coverSize, which cost arbitrarily small power of the hatted beta,
EVEN exponentiating back to mesh ratios. This says nothing about the truth of
the station analytic estimates themselves without those other inputs (see
assembly).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Dense
open Function Set Filter Asymptotics Lattice RG RG.Supply Next.Rank Next.Rank.Ship Next.Rank.Station
open scoped Topology BigOperators
variable {G : Gauge} (hG : G.Simple) {s : Sheet G} {w : Rolls s}
  {θ : Protection w} {W : Delays θ} (Y : Bar W)

def unitLog (w : Rolls s) (j : ℕ) : ℝ := Real.log ((w.L j).val : ℝ)
lemma length_gt (w : Rolls s) (j : ℕ) : 1 < ((w.L j).val : ℝ) := by
  exact_mod_cast (by have h := (w.large j).size; omega : 1 < (w.L j).val)
lemma positiveUnit (w : Rolls s) (j : ℕ) : 0 < unitLog w j := Real.log_pos (length_gt w j)
include hG
lemma scheduledHeight : Tendsto (preHat Y) atTop atTop := tendsto_atTop_add_const_left _ _
    (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos hG))

omit hG

def slim (Y : Bar W) (j : ℕ) (t : ℝ) : ℕ := Nat.floor (Real.log (preHat Y t) / unitLog w j)

include hG
lemma slimWindow (j : ℕ) : Tendsto (fun t : ℝ => (slim Y j t:ℝ)/t) atTop (𝓝 0) := by
  have hg := positiveUnit w j
  have he := scheduledHeight hG Y
  have hp : preHat Y=O[atTop] id :=
    (isLittleO_const_id_atTop _).isBigO.add ((isBigO_refl id _).const_mul_left _)
  have hv := ((Real.isLittleO_log_id_atTop.comp_tendsto he).trans_isBigO hp).tendsto_div_nhds_zero
  let l : ℝ := unitLog w j
  let a (t : ℝ) := Real.log (preHat Y t)
  have hh : Tendsto (fun t => a t / t / l) atTop (𝓝 0) := by
    have ha := hv.div_const l; rw [zero_div] at ha; exact ha
  refine squeeze_zero' ?_ ?_ hh
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht; positivity
  filter_upwards [he.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)] with t ht hp'
  rw [div_right_comm (a t)]
  exact div_le_div_of_nonneg_right (Nat.floor_le (div_nonneg (Real.log_nonneg ht) hg.le)) hp'.le

section ceiling
omit hG
lemma ceil_later {f : ℝ→ℝ} (h : f=o[atTop] Real.log) (he : ∀ᶠ x in atTop,0 ≤ f x) :
    (fun t : ℝ => ((Nat.ceil (f t) : ℕ):ℝ))=o[atTop] Real.log := by
  let g t := f t + 1
  refine IsBigO.trans_isLittleO (isBigO_iff.mpr ⟨1,?_⟩) (show g =o[atTop] Real.log from h.add Real.isLittleO_const_log_atTop)
  filter_upwards [he] with i hi
  simp only [one_mul,Real.norm_natCast, g]
  exact (Nat.ceil_lt_add_one hi).le.trans (Real.le_norm_self _)

lemma bumpSlim {u : ℝ} (hu : 1<u) {b : ℝ} (hb : 0≤b) :
    (fun t : ℝ => ((bump u b t:ℕ):ℝ))=o[atTop] Real.log := by
  apply ceil_later
  · refine ((Real.isLittleO_pow_log_id_atTop (n:=2) |>.comp_tendsto Real.tendsto_log_atTop).const_mul_left ((b+2) / Real.log u)).congr_left (fun x => ?_)
    unfold Vac.Numbers.P; dsimp only [comp_apply]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity), Real.log_pow, Real.log_exp]
    push_cast; ring
  refine Eventually.of_forall fun x => ?_
  apply div_nonneg _ (Real.log_pos hu).le
  have hp : 1 ≤ Vac.Numbers.P x := Real.one_le_exp (sq_nonneg _)
  exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hp hb) (one_le_pow₀ hp))

lemma moreSlim {u : ℝ} (hu : 1<u) :
    (fun t : ℝ => ((more u t:ℕ):ℝ))=o[atTop] Real.log := by
  let y s := ((Nat.ceil (Real.log s^2):ℕ):ℝ)
  have he : ∀ᶠ x in atTop, 1 ≤ y x ∧ 1 ≤ Real.log x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with x hx
    exact ⟨(one_le_pow₀ hx).trans (Nat.le_ceil (Real.log x^2)),hx⟩
  have hv : (fun x => Real.log (y x))=o[atTop] Real.log := by
    have hh : (fun t => Real.log 2 + 2*Real.log (Real.log t))=o[atTop] Real.log :=
        Real.isLittleO_const_log_atTop.add ((Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).const_mul_left _)
    refine IsBigO.trans_isLittleO (isBigO_iff.mpr ⟨1,?_⟩) hh
    filter_upwards [he] with x ⟨ht,hx⟩
    simp only [one_mul, Real.norm_of_nonneg (Real.log_nonneg ht)]
    apply le_trans _ (Real.le_norm_self _)
    calc
      _ ≤ Real.log (2 * (Real.log x)^2) := Real.log_le_log (zero_lt_one.trans_le ht)
        ((Nat.ceil_lt_add_one (sq_nonneg (Real.log x))).le.trans (by linarith only [one_le_pow₀ (n:=2) hx]))
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ (zero_lt_one.trans_le hx).ne'),Real.log_pow]; norm_num
  apply ceil_later
  · refine (hv.const_mul_left (10/Real.log u)).congr_left (fun x=>?_)
    change (10/Real.log u) * Real.log (y x) = Real.log (y x ^ (10:ℕ)) / _
    rw [Real.log_pow]; push_cast; ring
  exact he.mono fun _ hx => div_nonneg (Real.log_nonneg (one_le_pow₀ hx.1)) (Real.log_pos hu).le
end ceiling

lemma bench_slim (j : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ t in atTop, benchCost Y b j t ≤ slim Y j t := by
  have hx := positiveUnit w j
  apply (scheduledHeight hG Y).eventually
    (p:=fun t => bump (w.L j).val b t+more (w.L j).val t ≤ Nat.floor (Real.log t / unitLog w j))
  filter_upwards [((bumpSlim (length_gt w j) hb).add (moreSlim (length_gt w j))).def (inv_pos.mpr hx),eventually_gt_atTop (1:ℝ)] with t ht hy
  rw [Real.norm_of_nonneg (Real.log_pos hy).le] at ht
  apply Nat.le_floor
  push_cast
  rw [div_eq_inv_mul]
  exact (Real.le_norm_self _).trans ht
end YM.SharpGram.Dense
