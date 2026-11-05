import YM.RemainderComparison.Beacon.Prices
import YM.Next.MULTISOURCE.Wage

/-!
# Pricing exponential credits on the realized calendar

Keep hat and actual coupling distinct. All costs through here uniform on adequate
coupling tail across every scale, including arbitrary admissible period and cutoff. Turn,
mask/reset costs in later calls aren't assumed included. Clock threshold uses hats.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Beacon
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext.Repeat Height
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
section trajectory
variable (C : Levels G)
local notation "Z" => C.clock
local notation "x" => C.clock.hatBeta
local notation "w" => C.clock.forcedAllowance

lemma step_ratio (hG : G.Simple) : ∀ᶠ m in atTop, x (m+1) ≤ 2*x m := by
  have he := C.fits.mesh.eventually (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one))
  filter_upwards [C.S.divergent.eventually_gt_atTop 0,he] with m hm ht
  have hk : Real.log ((C.S.block m).val:ℝ) ≤ C.S.scale m := by
    change _ / _ < 1 at ht
    exact ((div_lt_one hm).mp ht).le
  unfold Calendar.hatBeta
  rw [Schedule.scale_succ]
  have hf : 0<G.slopeConstant:= Gauge.slopeConstant_pos hG
  nlinarith only [C.clock.bar_pos, mul_le_mul_of_nonneg_left hk hf.le]

lemma earned m : Target.earnings (x m)=(w m)^4 := by
  unfold Target.earnings Calendar.forcedAllowance
  rw [← Real.exp_nat_mul]; congr 1; unfold Calendar.monitor Vac.Numbers.P; push_cast; ring
lemma earned_le m : Target.earnings (x m) ≤ w m := by
  rw [earned]
  exact ((pow_le_pow_of_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by have h:0 ≤ (Z).monitor m:= Real.exp_nonneg _; exact neg_nonpos.mpr (Real.rpow_nonneg h _))) (show 1≤(4:ℕ) from by decide))).trans_eq (pow_one _)

-- Uniform super-polynomial absorption: adjacent comparison has no perturbative
-- β step identification in the proof. Needed in undoing book gauges.
lemma force_by (hG : G.Simple) (p : ℝ) (hp : 0 ≤ p) (b : ℝ) (hb : 0<b) :
    ∀ᶠ m in atTop, (x (m+1))^p * w m ≤ b := by
  let L:Side :=1
  have hL (q:ℝ) : betaF G q L=q:=by change q+_*Real.log ((1:ℕ):ℝ)=_; simp
  have hM m : w m= incomingK G L (x m) := by
    unfold Calendar.forcedAllowance incomingK Delay.fineMonitor; rw [hL]; rfl
  have hh := ((Rate.power (G:=G) (L:=L) (a:=p)).mul (incomingK_rate G L (-p-1))).mul_left ((2:ℝ)^p)
  filter_upwards [(YM.Multi.Wage.hat_tend hG C).eventually (hh.below (by linarith) _ hb),step_ratio C hG]
    with m hv hx
  let t:= x m
  have ht : 0<t:=zero_lt_one.trans (C.fits.delayed m)
  refine (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (zero_lt_one.trans (C.fits.delayed (m+1))).le hx hp) (show 0 ≤ w m from Real.exp_nonneg _)).trans ?_
  rw [Real.mul_rpow (show (0:ℝ) ≤ 2 by norm_num) ht.le,mul_assoc,hM]
  refine (le_abs_self _).trans ?_; simpa only [hL] using hv
end trajectory
section prices
variable {P : Teller G} (Q : Target G P) (L : Side) (u y : ℝ) (j : ℕ)
lemma seed (he : 1< betaF G y L) :
    (betaF G y L)^(-(1/2:ℝ))*Real.exp (-Q.mark L u y) ≤ Cash.armK Q L u y 0 j := by
  let F:= betaF G y L
  have hF:0 < F:=zero_lt_one.trans he
  have h := (Real.rpow_le_rpow_of_exponent_le he.le Q.start.le)
  have hp : 1 ≤ Reserves.polyPrice Q.ε j:= by
    have ht:= polynomial_cost Q.usable (le_refl (0:ℝ)) j
    simpa only [mul_zero,add_zero,one_pow, Real.exp_zero,mul_one] using! ht
  let k:=Q.costs L u 1 y 0
  have hm : F^(-(1/2:ℝ)) ≤ k.rootHit := le_trans h (show F^Q.rate≤ Real.exp _ + F^Q.rate from le_add_of_nonneg_left (Real.exp_pos _).le)
  have hr: k.q=1/2:=rfl
  have hh : 0 ≤ k.rootHit := (Real.rpow_pos_of_pos hF _).le.trans hm
  unfold Cash.armK; rw [pow_zero,inv_one,one_mul, mul_comm]
  have he : k.rootHit ≤ Q.overture L u y j := by
    unfold Target.overture Target.quantum Mixed.Costs.ceiling Reserves.extract Reserves.treeYield
    change k.rootHit ≤ polyPrice Q.ε _ * _ * (k.rootHit*k.q^0*_)
    simp only [Nat.cast_zero,pow_zero,mul_zero,sub_zero,Real.exp_zero,mul_one]
    rw [show (Q.costs L u 1 y 0).q=1/2 from hr]
    norm_num; nlinarith [mul_le_mul_of_nonneg_right hp hh]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  unfold Target.mergeScale; norm_num; linarith
end prices

-- MANY scales and expenses under one uniform ticket, purchasing from the *actual*
-- earnings hypothesis. No positivity of Income inferred from end convergence.
lemma mark_ready (C : Levels G) (hG : G.Simple) (n : ℕ) :
    ∀ᶠ m : ℕ in atTop, let x:= C.clock.hatBeta m; let t:=C.clock.hatBeta (m+1)
      ∀ L, betaF G x L=t → ∀ (P : Teller G) (Q : Target G P) u j,
        Cash.armK Q L u x 0 j ≤ Target.earnings x →
          (grow G L x)^n ≤ Real.exp (Q.mark L u x) := by
  let p:ℝ:=(3/8:ℝ)*n
  have hp : 0≤p:=by unfold p; positivity
  filter_upwards [force_by C hG (p+1/2) (by linarith only [hp]) 1 zero_lt_one] with m hx x t L hL P Q u j hu
  have ht : 1<t:= C.fits.delayed _
  have hb : 0<t:= zero_lt_one.trans ht
  have hy := ((seed Q L u x j (hL ▸ ht)).trans hu).trans (earned_le C m)
  rw [hL] at hy
  change t^(p+1/2) * _ ≤ 1 at hx
  have hh := (mul_le_mul_of_nonneg_left hy (Real.rpow_pos_of_pos hb (p+1/2)).le).trans hx
  unfold grow; rw [hL, ← Real.rpow_mul_natCast hb.le]
  have hv : p+1/2 + -(1/2)=p:=by ring
  rw [← mul_assoc, ← Real.rpow_add hb,hv, Real.exp_neg, ← div_eq_mul_inv] at hh
  exact (div_le_one (Real.exp_pos _)).1 hh

lemma grow_gap (G : Gauge) (L : Side) (x β : ℝ) (ht : 1<betaF G x L)
    (h : inBand (betaF G x L) β) : (grow G L x ^ 2)⁻¹ ≤ 2 * (Real.sqrt β)⁻¹ := by
  let H:=betaF G x L
  have hp:0<H:= zero_lt_one.trans ht
  have hg : 0 < Real.sqrt H:= Real.sqrt_pos.2 hp
  have hh : (Real.sqrt H)⁻¹/2 ≤ (Real.sqrt β)⁻¹:= (band_gap _ β hp h).1
  unfold grow; rw [← Real.rpow_mul_natCast hp.le]
  apply (inv_anti₀ hg ((Real.sqrt_eq_rpow ..).trans_le (Real.rpow_le_rpow_of_exponent_le ht.le ?_))).trans
  · linarith
  push_cast
  norm_num

lemma coarse_δ (T:Levels G) (m:ℕ) : δE (T.clock.hatBeta m) ≤ 1 := by
  have h:T.clock.hatCoupling m ≤ 1:= by
    unfold Calendar.hatCoupling; exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (T.fits.delayed _).le)
  change (T.clock.hatCoupling m)^ ((11:ℝ)/5) ≤ _
  exact Real.rpow_le_one (inv_nonneg.mpr (Real.sqrt_nonneg _)) h (by norm_num)

-- enough power for the forced divisor on the incoming ONE-step census charges;
-- later merges must withdraw from their actual hit norm (not simply assume count-free).
lemma insurance (C : Levels G) (hG : G.Simple) (j : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ β, β∈Shoot.band C (m+1) →
       C.clock.forcedAllowance m ≤ ((Real.sqrt β)⁻¹)^j := by
  let a:ℝ:=1/2*j
  have hp : 0≤a:=by unfold a; positivity
  let b : ℝ:=(2^j:ℝ)⁻¹; have hb:0<b:=by unfold b; positivity
  filter_upwards [force_by C hG a hp b hb] with m hx β hβ
  let x:=C.clock.hatBeta (m+1); let g:=(Real.sqrt β)⁻¹
  have hy:0 < x:= zero_lt_one.trans (C.fits.delayed _)
  have hu : Clock.gap x/2 ≤ g:= (band_gap _ _ hy (trial_in hβ)).1
  have he: 0 ≤ Clock.gap x / 2 := div_nonneg (Clock.gp hy).le (by norm_num)
  apply le_trans ?_ (pow_le_pow_left₀ he hu j)
  unfold Clock.gap; rw [div_pow, inv_pow,div_eq_mul_inv,Real.sqrt_eq_rpow,← Real.rpow_mul_natCast hy.le]
  change C.clock.forcedAllowance m ≤ (x^a)⁻¹*b
  rw [mul_comm,← div_eq_mul_inv]; exact (le_div_iff₀ (by positivity : 0 < x^a)).mpr (by rw [mul_comm]; exact hx)
end YM.RemainderComparison.Beacon
