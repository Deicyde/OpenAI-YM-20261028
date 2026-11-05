import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Endow
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Regale
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Stocks
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Length
import YM.Progress.CLASSICAL_KIN_RECURSION.Merge
import YM.Push.LOOP_COEFFICIENT.History.Ledger
import YM.Push.STRESS_FLUX.Rebate
import YM.UVNext.COUPLING_RESET.Advance
/-!
# Purchases through all scale parameters of a stretch
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst Pump Ac Baler Glyph Tapes Marker
open Display Display.Docking Display.Sew Value Flux SectorNext.Vacuum Station Perch
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

def weather (s : ℝ) (n : ℕ) := rollup s n * advance s
def sailboat (s : ℝ) (n : ℕ):= rollup s n * advance s^3
lemma advancePay (C a : ℝ) (h : 0<a) : ∀ᶠ s in atTop, bill C s ≤ s^a:= by
  rcases le_or_gt C 0 with hC|hC
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with s hs; exact (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (Perch.boil_pos _) hC)).trans (Real.one_le_rpow hs h.le)
  filter_upwards [advancement (a/C) 2 (div_pos h hC), eventually_gt_atTop (0:ℝ)] with s he hs
  unfold bill; rw [Real.rpow_def_of_pos hs]; apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_right he hC.le).trans_eq (by field_simp)
lemma luxury (i : Purse) : ∀ᶠ s in atTop,Line i.era i.goal 0 s ≤ advance s := by
  have hm: (6:ℝ) ≤ i.goal:=by exact_mod_cast i.tolerance
  filter_upwards [advance_large ((i.goal:ℝ)-3), advances.eventually_ge_atTop 1] with s ht hp
  unfold Line firstN fareP Perch.bill; rw [mul_zero,zero_add,← Real.exp_sub];
  refine max_le hp ?_; refine le_trans ?_ ht; apply Real.exp_le_exp.mpr; linarith only
lemma spray_side (a : ℝ) (ha : a< -(1/200)): ∀ᶠ s:ℝ in atTop,∀ x∈Set.Icc (s/2) s,x^a≤ spray s:= by
  let d:=(1/2:ℝ)^a
  filter_upwards [slack d ha,eventually_gt_atTop (0:ℝ)] with s h hs x hx
  apply (Real.rpow_le_rpow_of_nonpos (half_pos hs) hx.1 (by linarith only [ha])).trans
  rw [div_eq_mul_inv,Real.mul_rpow hs.le (by positivity),mul_comm];
  exact (le_of_eq (show (2:ℝ)⁻¹^a*s^a=d*s^a by unfold d; rw [one_div])).trans h
lemma garlicPay : ∀ᶠ s in atTop,∀ x∈Set.Icc (s/2) s,Grid.garlic (retime x)≤ spray s:= by
  obtain ⟨p,hp⟩:= eventually_atTop.mp burst_limit
  filter_upwards [spray_side (-(1/48)) (by norm_num), Perch.half.eventually_ge_atTop p, eventually_gt_atTop (0:ℝ)] with s h he ht x hx
  exact (Real.rpow_le_rpow_of_nonpos ((half_pos ht).trans_le hx.1) (hp _ (he.trans hx.1)).1 (by norm_num : -(1/48:ℝ)≤0)).trans (h x hx)
lemma staff_burn (C : ℝ) (a : ℝ) (hC :0<C) (ha : 0<a) : ∀ᶠ s in atTop,a*Real.log s ≤ C* hot (s/2)^2 := by
  have he:0<a/C:=div_pos ha hC
  filter_upwards [(Perch.y_rate.comp Perch.half).eventually_ge_atTop (Real.log (a/C) + 1),
    (Perch.y_rate.comp Perch.half).eventually_ge_atTop 1,Perch.logspan,eventually_gt_atTop (1:ℝ)] with s hv h hy hs
  let z:=y (s/2); change 1≤ z at h; change _ ≤ z at hv
  have hm : z ≤ z^((3:ℝ)/2):= le_trans ((Real.rpow_one _).symm.le) (Real.rpow_le_rpow_of_exponent_le h (by norm_num))
  have hQ : a/C* Real.log s ≤ hot (s/2)^2:= by
    apply (Real.log_le_log_iff (mul_pos he (Real.log_pos hs)) (pow_pos (Real.exp_pos _) _)).1
    rw [Real.log_mul he.ne' (Real.log_pos hs).ne', Real.log_pow];
    rw [Real.log_exp,Nat.cast_ofNat]; change Real.log (a/C)+y s≤ 2*z^((3:ℝ)/2); change _≤ z+1 at hy; linarith only [hv,h,hy,hm]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hQ hC.le); apply le_of_eq; field_simp

lemma next_rate (s : ℝ) (hs : 0 < s) (ha : 17 ≤ advance s) (n : ℕ) : spray s+16*sailboat s n ≤ rollup s (n+1):=by
  let z:=rollup s n; let y:=advance s
  have hy:1 ≤ y:= (by linarith only [ha] : 1 ≤ advance s)
  have ht:spray s≤ z:= floor_spray hs hy n
  have hv:z ≤ sailboat s n:= le_mul_of_one_le_right ((Real.rpow_pos_of_pos hs (-(1/200):ℝ)).le.trans ht) (one_le_pow₀ hy)
  have hQ:0 ≤ sailboat s n:= ((Real.rpow_pos_of_pos hs (-(1/200):ℝ)).le.trans ht).trans hv
  rw [each_count,show rollup s n*advance s^4= sailboat s n * advance s by unfold sailboat; ring]; linarith only [hQ, ht,hv,mul_le_mul_of_nonneg_left ha hQ]
lemma pay_sparks (P : Purse) (L : Side) : ∀ᶠ s:ℝ in atTop,∀ x∈Set.Icc (s/2) s,∀ y∈Set.Icc (s/2) s,
    wilt (walls x)*((Fintype.card (Site L):ℝ)*(salary (load P.era+1)* Perch.gas P.era.coast y)) ≤ spray s:= by
  let c:= (33:ℝ)^4 * ∑' i,welter i; let w:=(Fintype.card (Site L):ℝ)*salary (load P.era+1)
  have h:0≤c:=mul_nonneg (by positivity) (tsum_nonneg fun i=>by unfold welter; positivity)
  have ht:0≤w:=mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  let a:=P.era.coast.a
  filter_upwards [staff_burn a 2 P.era.coast.posA (by norm_num), Paint.q_power 4 1 zero_lt_one, advancePay 1 1 zero_lt_one, Perch.half.eventually_ge_atTop (Real.exp 1),Perch.half.eventually_ge_atTop 1, slack (c*w) (by norm_num:(-(1:ℝ))< -(1/200))] with s he hv hy hf hX hk x hx y hY
  let p:=Perch.gas P.era.coast y
  have hs:0<s:=zero_lt_one.trans_le ((hX.trans hx.1).trans hx.2)
  have hm:p≤ s^(-(2:ℝ)):= by
    rw [Real.rpow_def_of_pos hs]; apply Real.exp_monotone
    change -a* (hot y)^2≤_; have h:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le (Perch.hot_mono hf hY.1) 2) P.era.coast.posA.le; change a*hot (s/2)^2 ≤ a*hot y^2 at h; linarith only [he,h]
  have hh:wilt (walls x) ≤ c*s^ (1:ℝ):= by
    rw [show wilt (walls x)=c*(walls x:ℝ)^4 by unfold wilt c; ring];
    exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (wall_mono (hX.trans hx.1) (hX.trans (hx.1.trans hx.2)) hx.2)) _).trans (hv.trans hy)) h
  rw [← mul_assoc (Fintype.card (Site L):ℝ) (salary (load P.era+1))]; change wilt _*(w*p) ≤ _
  apply (mul_le_mul hh (mul_le_mul_of_nonneg_left hm ht) (mul_nonneg ht (Real.exp_pos _).le) (by positivity)).trans
  rw [mul_mul_mul_comm c, ← Real.rpow_add hs, show 1+ -(2:ℝ)= -1 by norm_num]; exact hk
end YM.PhysicalNext.InteractingRank.Soft
