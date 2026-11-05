import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter
/-! # Purchasing the second run of the K packing (pre actual turn), even when
 t already strong exact β. Pay a finite POWER loss. Use AFTER cap assumptions E hatch. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Marlin
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain 
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable (G : Gauge) (L : Side)
section toll
variable {a b c q p : ℝ} {B : ℕ}
lemma pennies (hq: 0 < q) (hd:0 < p) (ha:0 ≤ a) (hv:0≤b) (hp : a ≤ q/8) (hh : q*p ≤ 1) (hu : b≤1)
    (ht : (B+B+1:ℕ)^4*((1/8)*p⁻¹+2*b) ≤ (1:ℝ)) (he : p*b ≤ (1:ℝ)/8) :
    ∃ κ, Payments.Rates B q a b κ := by
  let κ:= -Real.log (q*p); have h0 : 0 ≤ κ:= neg_nonneg.mpr (Real.log_nonpos (mul_pos hq hd).le hh)
  have h: Real.exp (-κ)=q*p:= by unfold κ; rw [neg_neg,Real.exp_log (mul_pos hq hd)]
  have hκ : Real.exp κ=(q*p)⁻¹ := by unfold κ; rw [Real.exp_neg,Real.exp_log (mul_pos hq hd)]
  let g:= (1/8)*(p:ℝ)⁻¹+2*b
  let W:= Payments.inflation a b κ
  have hb: W≤g:=by
    unfold W g Payments.inflation; apply add_le_add _ le_rfl; rw [hκ]; apply (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (mul_pos hq hd).le)).trans_eq; field_simp
  have hx:0 ≤ W:= by unfold W Payments.inflation; positivity
  have hP:(B+B+1:ℕ)^4*W ≤ (1:ℝ):= (mul_le_mul_of_nonneg_left hb (by positivity : 0≤((B+B+1:ℕ):ℝ)^4)).trans ht -- cast issue
  have hX : W ≤ 1:= le_trans (le_mul_of_one_le_left hx (one_le_pow₀ (a:=((B+B+1:ℕ):ℝ)) (by exact_mod_cast (show 1≤B+B+1 by omega)))) hP
  have hy:= Real.abs_exp_sub_one_le (show |W|≤1 from (abs_of_nonneg hx).trans_le hX); rw [abs_of_nonneg hx] at hy
  refine ⟨κ,h0,ha,hv,hu,hP,?_⟩; change Real.exp (-κ)*(Real.exp W-1) ≤ _; rw [h]
  have hi:0<q*p:= mul_pos hq hd
  apply (mul_le_mul_of_nonneg_left (((le_abs_self _).trans hy).trans (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 2))) hi.le).trans
  rw [mul_assoc]; apply mul_le_of_le_one_right hq.le
  calc _ = 2*((1/8)+2*(p*b)):= by unfold g; field_simp
       _ ≤ _ := by linarith
open Clock
variable (F : Postage) (A : Time.Forecast F)
local notation "M" => (fun x=> betaF G x L)
local notation "P" => (fun x=> (M x)^((1:ℝ)/16))
lemma bound_up : ∀ᶠ x in atTop, ∀ b:ℝ,Next.Scheduling.inBand (betaF G x L) b→ (A.pair.strong (M x) b)*P x≤ 1:= by
  let h:= A.hard/4; let p x:= Delay.fineMonitor G L x
  have ht : 0<A.hard:= F.pos.trans A.surplus; have he : 0 < h:=by unfold h; positivity
  let k x:= Real.exp (-h*p x^(2:ℕ)); have hk : Rate G L (-1) k:= by simpa only [k,Real.rpow_two] using! Rate.monitor_cutoff (G:=G) (L:=L) (a:=-1) he (show 0<(2:ℝ) by norm_num)
  filter_upwards [Delay.shift_pos G L,(((hk.mul_left A.pair.C).mul (Rate.power (a:=(1:ℝ)/16))).below (by norm_num) 1 zero_lt_one)] with x hx hK b hB
  obtain ⟨ha,hp⟩:= band_gap (M x) b hx hB; let y:=M x; have hv:0< Clock.gap (M x):= Clock.gp hx
  have hb :0< Clock.gap b:= (half_pos hv).trans_le ha
  have hi : 0 < Instrument.plain.P y:= Clock.wp Instrument.plain.center y
  have hu : Instrument.plain.t y / Clock.gap b ≥ p x/ 2:= by
    rw [ge_iff_le,le_div_iff₀ hb]; unfold Instrument.t; rw [← (show Instrument.plain.P y=p x from Clock.watch_two _)]
    change _≤ Clock.gap y * _; linarith only [mul_le_mul_of_nonneg_left hp hi.le]
  let v₀:= Instrument.plain.t y / Clock.gap b; let a:= A.hard
  unfold Payments.Pairing.strong; apply le_trans _ ((le_abs_self _).trans hK)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (x:=y) hx.le _); change A.pair.C*Real.exp (-a*v₀^2) ≤ _
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) A.pair.C_nonneg
  have hh : p x / 2 ≤ v₀ := hu; unfold h; nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (half_pos (Delay.monitor_pos G L x)).le hh 2) ht.le] -- arithmetic
lemma pricingBuy : ∀ᶠ x in atTop,∀ β:ℝ, Next.Scheduling.inBand (betaF G x L) β→∀ a b:ℝ,let v:= A.pair.strong (M x) β
    0 ≤ a → 0 ≤ b → a ≤ v/8 → b ≤ (M x) ^ (-(1/8:ℝ)) → ∃ κ, Payments.Rates (radiusB x) v a b κ:= by
  let z x:= (M x)^(-(1/8:ℝ)); have he : Rate G L (-(1/8)) z:= Rate.power
  have hp : Rate G L (-(1/16)) (fun x=> (P x)⁻¹):= by apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; rw [Real.rpow_neg hx.le]
  let B x:=radiusB x
  have hv : Rate G L 0 (fun x=> ((B x+B x+1:ℕ):ℝ)^4):= by simp only [Nat.cast_add,Nat.cast_one]; simpa only [zero_mul] using! (((Rate.radius_price (G:=G) (L:=L)).add Rate.radius_price).add (Rate.const 1)).pow 4
  filter_upwards [he.below (by norm_num) 1 zero_lt_one,bound_up G L F A, Delay.shift_pos G L,(hv.mul ((hp.mul_left (1/8)).add ((he.mul_left 2).weaken (by norm_num)))).below (by norm_num) 1 zero_lt_one, ((Rate.power (a:=1/16)).mul he).below (by norm_num) (1/8) (by norm_num)] with x he' hy hz hK hv β hβ a b v h hh hx hP
  have hv₀:0<v:= mul_pos (zero_lt_one.trans_le (le_max_left 1 A.coeff)) (Real.exp_pos _); have hY : 0<P x:=Real.rpow_pos_of_pos hz _
  refine pennies hv₀ hY h hh hx (hy _ hβ) (hP.trans ((le_abs_self _).trans he')) ?_ ((mul_le_mul_of_nonneg_left hP hY.le).trans ((le_abs_self _).trans hv))
  exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hP (by norm_num : (0:ℝ)≤2))) (show 0≤ ((B x+B x+1:ℕ):ℝ)^4 by positivity)).trans ((le_abs_self _).trans hK)
end toll
end YM.PhysicalNext.Repeat.Marlin
