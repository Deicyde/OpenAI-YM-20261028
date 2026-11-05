import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Acreage

/-!
# Packet price thresholds. Seeds uniformly post per epoch, operational API
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Grid
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Oriented Push.AbsoluteSums Pressure.Stores
    AnalyticNext.ConnectedActivity GaugeRoute Packets Display Display.Sew Pot Marker Milk
    Local Next.SectorChange.Rows Gaussian Schur Wisps Next.Rank Next.Rank.Perch Next.Rank.Value Next.Rank.Flux Vale Display.Docking Next.Scheduling
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ENNReal
variable {c f : Side} {G : Gauge} {S : StepData c f} {L : Side} {x W t q Κ r l a o C δ η e : ℝ} {A : Stores S} {v : Dyed G S} {P : Teller G} {F : Forest S.ratio}

-- α times flow: uniform area pensions and optional masks
-- x=retime x actual, where S β earn. width AFTER Teller.P.
lemma postage (P : Patch) (G : Gauge) (x : ℝ) (S : StepData c f) (h : S.patch=P) (i : Core S x):
    let b:=1+((300*radiusB x+1:ℕ):ℝ)
    ((Pot.mined i).card:ℝ) * Jewels.attrition S.patch ≤
      4*(marks G P*b^4)*Jewels.attrition P*i.val.shares:= by
  intro b
  subst P
  have ht : ((Pot.mined i).card:ℝ) ≤ 4*(i.val.shares)*(marks G S.patch*b^4):= by
    refine Aff.count_dome (toes S) _ (gauges S.patch).le (fleck_notice S G) ?_
    intro j hj; obtain ⟨k,hk,hv⟩:= luck hj
    exact Aff.facesLocal i.val hv (by rw [separation_comm]; have hh := strides S j k hk; omega)
  apply (mul_le_mul_of_nonneg_right ht (Jewels.attrition_nn _)).trans_eq; ring

lemma hopper (L : Side) (G : Gauge) (n m : ℕ) (c : ℝ) (ha : 0<a) : ∀ᶠ x in atTop,
    let u:= retime x; let y:= betaF G x L
    c*(1+(radiusB u:ℝ))^n*(Real.log u)^m ≤ a*hot y ^2:= by
  let C:= max c 0
  let s:= Real.sqrt a; have hs:0<s:=Real.sqrt_pos.mpr ha
  filter_upwards [burst_limit, Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop (1:ℝ), (Work.E01.betaF_tendsto G L).eventually
    (hotspot (2*n+m) (C*6^n * 2^m) s hs)] with x hx hp h1 h
  intro u y; let z:=Real.log y; have hS : 0<x:= zero_lt_one.trans h1; have hU : 0<u:= lt_of_lt_of_le hS hx.1
  have hY: Real.log x ≤ z:= Real.log_le_log hS (le_add_of_nonneg_right (Work.E04.shift_nonneg G L))
  have hv : 1≤z:= hp.trans hY
  have hz : 1≤Real.log u:=hp.trans (Real.log_le_log hS hx.1)
  have hf : Real.log u ≤ 2*z:= by
    apply (Real.log_le_log hU hx.2.1).trans; rw [Real.log_pow]; push_cast; linarith only [hY]
  have he : 1+(radiusB u:ℝ) ≤ 6*z^2:= by
    have he:(radiusB u:ℝ)≤ (Real.log u)^2+1:= (Nat.ceil_lt_add_one (sq_nonneg _)).le
    nlinarith only [pow_le_pow_left₀ (zero_le_one.trans hz) hf 2,hv,he]
  have hh : a= s^2 := (Real.sq_sqrt ha.le).symm
  calc
    _ ≤ C*(6*z^2)^n*(2*z)^m := by gcongr; exact le_max_left .. -- positivity
    _ = C*6^n*2^m * z^(2*n+m):= by rw [pow_add,pow_mul]; simp only [mul_pow]; ring
    _ ≤ _:= hh.symm ▸ h

lemma coast_run (G : Gauge) (K : ℝ) (hp : 0<K) (η : ℝ) (hη : 0<η) (D : Patch) : ∀ᶠ x in atTop,
    let u:= retime x; let y:=betaF G x D.L
    ∀ β : ℝ,y/2≤ β → coast G (η*fiery G u D.L/coupling β) K D u≤ u^(-(2:ℝ)):=by
  let B:= marks G D; let c:=8*K*B; let a:=η^2/8
  have hc:0<c:=by unfold c B; have ht:= gauges (G:=G) D; positivity
  have ha:0<a:=by unfold a; positivity
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,(Work.E01.betaF_tendsto G D.L).eventually_gt_atTop 0,
    burst_limit, crossfade G D.L, hopper D.L G 4 1 (3*c*2^4) ha,eventually_gt_atTop (0:ℝ)] with x hx hh hv h hC hp'
  intro u y β he; let q:= fiery G u D.L
  let H:= 8*K*density G D (radiusB u); have hB:0<H:= by unfold H density; have ht:= gauges (G:=G) D; positivity
  have hβ :0<β:= (half_pos hh).trans_le he
  have hy : (q*q)*β * η^2 ≥ a*hot y^2:= by
    have ht : Paint.phase y ≤ 2*q:= h.2.2.2
    have hv : Paint.phase y ^2 = hot y^2/y:= by unfold Paint.phase Vac.Numbers.Hat; rw [mul_pow,inv_pow,Real.sq_sqrt hh.le]; ring
    have h₁ := pow_le_pow_left₀ (show 0≤Paint.phase y from h.1.le) ht 2; rw [hv,div_le_iff₀ hh] at h₁
    have hb : hot y^2 ≤ 8 * q^2 * β:= by nlinarith only [h₁,mul_le_mul_of_nonneg_left (show y ≤ 2*β by linarith only [he]) (sq_nonneg q)]
    unfold a; nlinarith only [mul_le_mul_of_nonneg_left hb (sq_nonneg η)]
  have hl : 1≤ Real.log u:= hx.trans (Real.log_le_log hp' hv.1); let A:=(η*q/coupling β)^2
  have hρ : 3*H*Real.log u≤A:= by
    unfold H density; push_cast; let B₀:ℝ:=radiusB u; let z:= hot y; let l:= Real.log u
    have hz:0≤B₀:=Nat.cast_nonneg _; have hf : 0≤l:= zero_le_one.trans hl
    calc
      _ = 3*c*(1+2*B₀)^4*l:= by unfold c; ring
      _ ≤ 3*c*(2*(1+B₀))^4*l:=by gcongr; linarith only
      _=3*c*2^4*(1+B₀)^4*l:=by rw [mul_pow]; ring
      _ ≤ a*z^2:= by simpa only [pow_one] using hC
      _ ≤ _:= hy.trans_eq (by unfold A coupling; rw [div_pow,inv_pow,Real.sq_sqrt hβ.le]; field_simp)
  unfold coast damp; rw [Real.rpow_def_of_pos (hp'.trans_le hv.1)]; apply Real.exp_monotone
  change 1/4 - H⁻¹ * A ≤ _; have hx : 3*Real.log u ≤ H⁻¹*A:= by rw [← div_eq_inv_mul]; apply (le_div_iff₀ hB).2; linarith only [hρ]
  linarith only [hl,hx]

lemma cornfield (G : Gauge) (D : Patch) (a : ℝ) (ha : 0<a) : ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f), S.patch=D → ∀ (v : Dyed G S) (W) (M : Plate v (retime x) W) r,
     let y:=betaF G x D.L; let b:=a*hot y^2
     1≤r → r≤Real.exp (b/4)→ S.patch.Branches S.kernel G →
     ∀ (p:Pilot G S (retime x)) (i : Rung S (retime x)), M.base (rips i) p ≤ -b*(rips i).val.shares → r*|atomP W v M (Sum.inl i) p|≤ (retime x^(-(4:ℝ)))^(rips i).val.shares:= by
  let t:=Jewels.attrition D; let m:=marks G D; have hm : 0 < m:= gauges D; have ht:0≤ t:= Jewels.attrition_nn _
  let c:=4*m*300^4*t
  filter_upwards [hopper D.L G 4 0 c (show 0<a/4 by linarith), hopper D.L G 0 1 4 (by linarith : 0<a/2), tall_limit.eventually_gt_atTop 0] with x hx hf hX c' f S hs v W M r
  intro y b hr hR hU p i he; let u:=retime x
  let O:=rips i; let s:ℝ:=O.val.shares
  have hh:1 ≤ s:= Nat.one_le_cast.mpr (shares_nonzero S _ _ O.property)
  have hz: ∏ j∈ mined O,|v.ask W p j|≤ Real.exp (b*s/4):= by
    apply le_trans (b:=∏ _j∈ mined O, Real.exp t)
    · apply Finset.prod_le_prod; intro i _; exact abs_nonneg _
      intro j _; let g:=v.ask W p j; have h: |g|+1≤ t:=(v.attrition W hU j p).trans_eq (congr_arg _ hs); linarith only [h,Real.add_one_le_exp t]
    rw [← Real.exp_sum,sum_const,nsmul_eq_mul];apply Real.exp_monotone
    let B:= radiusB u
    have ht : Jewels.attrition S.patch=t:= hs ▸ rfl
    refine (show _ ≤ 4*(marks G D*(1+(300*B+1:ℕ))^4)*t*s from by rw [← ht]; exact (show ((Pot.mined O).card:ℝ)*Jewels.attrition S.patch ≤ 4*(marks G D*(1+(300*B+1:ℕ))^4)*Jewels.attrition S.patch*s from by rw [ht]; have hz := postage D G u S hs O; rw [ht] at hz; exact hz)).trans ?_
    calc
      _ ≤ 4*(m * (300*(1+(B:ℝ)))^4)*t*s:= by push_cast; gcongr; linarith only
      _= c*(1+(B:ℝ))^4 * (Real.log u)^0 *s:= by unfold c; ring
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right hx (zero_le_one.trans hh)]
  change r*|checkIn v i p*(Real.exp (M.base _ _) * _)|≤ _
  let g:=a*hot y^2; have hB:0≤g:=mul_nonneg ha.le (sq_nonneg _)
  have hf:4*Real.log u ≤ g/2:=by rw [show g/2=a/2*hot y^2 by unfold g;ring]; change 4*(1+(radiusB u:ℝ))^0* (Real.log u)^1≤a/2* hot y^2 at hf; simpa only [pow_zero,pow_one,mul_one] using hf
  rw [Real.rpow_def_of_pos hX,← Real.exp_nat_mul, abs_mul, abs_mul,Real.abs_exp,abs_prod]
  have hk:|checkIn v i p|≤1:=by unfold checkIn; split <;> simp
  apply (mul_le_mul hR (mul_le_mul hk (mul_le_mul (Real.exp_monotone he) hz (prod_nonneg fun i _=>abs_nonneg _) (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le (prod_nonneg fun i _=>abs_nonneg _)) zero_le_one) (mul_nonneg (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le (prod_nonneg fun i _=>abs_nonneg _))) (Real.exp_pos _).le).trans
  rw [one_mul,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
  change b/4+_ ≤ _; nlinarith only [mul_le_mul_of_nonneg_left hh hB,mul_le_mul_of_nonneg_right hf (zero_le_one.trans hh)]
end YM.PhysicalNext.InteractingRank.Pump.Grid
