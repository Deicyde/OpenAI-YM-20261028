import YM.AnalyticBridge.VERIFIED_RESET_STEP.Dial
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Tables
import YM.Extra.WILSON_STARTUP.Clock
import YM.Next.ROTATIONS.Nodes
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Wisps
import YM.UVNext.COUPLING_RESET.Precision
import YM.UVNext.PRICED_KERNELS.Degree

/-! E §freset numerical inequalities at one fixed transition (including
within-stage recurrence). Can be increased by post-L requests before W/I
are finalized. Provides NO predictions that a reclosure/inheritance/HRGv
calculation meets these pre-merge output costs; distinguishes the pre-L
fraction there from the post-L absolute hit exponents. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Time
open Filter Function Set Lattice Wilson RG Precision Collection Next.Scheduling Clock Instrument UVNext.CouplingReset Progress.DirectedRecipe
open scoped Topology BigOperators Classical
variable (G : Gauge) (S : Stage)

/-- Rate needed on the same raw output polymer activity (+1 support
exponent) before adding ANY of the new soft labels. Input to Gaussian work.
After-L: can tune as close to F.rate as desired but genuinely larger here. -/
structure Forecast (F : Postage) where
  coeff : ℝ
  coeff_pos : 0 < coeff
  hard : ℝ
  surplus : F.rate < hard

def Forecast.pair {F : Postage} (A : Forecast F) : Payments.Pairing F :=
    ⟨max 1 A.coeff,le_max_of_le_left zero_le_one, A.hard,A.surplus,0,0,1/2,by norm_num⟩

lemma threshold_aligned (x : ℝ) (hx : 0 < x) :
    plain.t x = Vac.Numbers.theta x ∧ WilsonStartup.Timing.temp (Real.log x) = plain.t x := by
  have he : plain.P x = Real.exp ((Real.log (Real.log x))^2) := Clock.watch_two x
  rw [Instrument.t,he]; refine ⟨rfl,?_⟩
  unfold WilsonStartup.Timing.temp gap
  rw [Real.exp_add,Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx,Real.exp_neg]; congr 3; ring

lemma small_expenses (U c : ℝ) : ∀ᶠ x : ℝ in atTop, U * (1+(cover x:ℝ))^4 * plain.t x ≤ gap (x+c)^((1:ℝ)/2) := by
  have he : Tendsto (fun x => (1+(cover x:ℝ))^4 * plain.P x * gap x ^ ((1:ℝ)/2)) atTop (𝓝 0) := by
    have hs := (ceiling_cheaper 2 1 4 one_lt_two zero_lt_one).mul (light 2 2 (1/2) (by norm_num))
    rw [mul_zero] at hs; refine hs.congr fun x => ?_; rw [Real.rpow_one,Real.rpow_two]; change _ = _ * watch 2 x * _
    field_simp [(wp 2 x).ne']
  have hf := (he.const_mul (2*U)).eventually (gt_mem_nhds (show (2*U)*0<1 by linarith))
  filter_upwards [hf,eventually_gt_atTop (0:ℝ),(similar_gap_power ((1:ℝ)/2)) 2 one_lt_two, just_near c] with x h hx hQ hN
  have h0 := gp hx
  have hx' := Real.rpow_pos_of_pos h0 ((1:ℝ)/2)
  unfold Instrument.t; rw [show gap x = gap x ^ ((1:ℝ)/2) * gap x ^ ((1:ℝ)/2) by rw [← Real.rpow_add h0]; norm_num]
  exact le_trans (by change _ ≤ gap x ^ ((1:ℝ)/2)/2; nlinarith only [mul_lt_mul_of_pos_right h hx'])
    ((div_le_iff₀ (by norm_num)).mpr (by linarith only [hQ _ _ (same x) hN]))

lemma lows (e : Exchange) (F : Postage) {x y θ L β : ℝ} (hL : 0 < L) (hy : 1 < y) (hb : inBand y β) :
    let T := e.cost * F.switch plain e.cost L θ x y (gap β)
    δE y / 16 ≤ T ∧ T ≤ T + F.bundle plain θ x y * (plain.t x)^3 := by
  intro T
  have he := lt_of_lt_of_le zero_lt_one e.ok.2.2.1
  have h0 : 0 < gap y := gp (by linarith)
  have hd : 0 ≤ δE y := Real.rpow_nonneg h0.le _
  have hg : 0 < gap β := lt_of_lt_of_le (half_pos h0) (band_gap y β (by linarith) hb).1
  have ht : 0 ≤ plain.t x := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (wp _ _).le
  have hM : 0 ≤ F.bundle plain θ x y := by
    have hp : 0 < plain.P y := wp _ _; have := F.h_ge; have := Real.rpow_pos_of_pos hp θ; unfold Postage.bundle LevelCost; positivity
  have hr : 0 ≤ F.residual plain θ x y (gap β) := by unfold Postage.residual; positivity
  constructor
  · apply le_trans (b:=e.cost * ((1 / (16 * e.cost))*δE y)) (le_of_eq (by field_simp))
    unfold T Postage.switch
    gcongr
    linarith [div_nonneg he.le hL.le,mul_nonneg (div_nonneg he.le hL.le) hd]
  exact le_add_of_nonneg_right (mul_nonneg hM (pow_nonneg ht _))

/-- All post/band arithmetic to use with purchases at the *actual* L and
forecast; no positive lower bound on theta needed by these particular gates.
`y=x+c` with c≥0 required (no flow of true β built into that shift). -/
lemma cash {F : Postage} (A : Forecast F) (U : ℝ) (_hU : 0 ≤ U) (c : ℝ) (hc : 0 ≤ c) : ∀ᶠ x : ℝ in atTop,
    let y := x+c; let H := credit G S * δE x
    ∀ p : BudgetPoint, Same S p → p.B=cover x → p.threshold=plain.t x →
      (S.clip.direct ≤ 1 → WilsonStartup.Decent S.clip p) ∧ Geo.Width p S.clip S.width ∧
      ∀ e : Exchange, ∀ L : ℝ,0<L → ∀ α θ β : ℝ, |α| ≤ U → inBand y β →
        let T := e.cost * F.switch plain e.cost L θ x y (gap β)
        let rate := Payments.Pairing.kGoal F y β
        let δ := δE x / 32
        let γ := Real.exp (-rate)
        H ≤ T ∧ δ ≤ T + F.bundle plain θ x y * (plain.t x)^3 ∧ Fees G p S.clip S.width S.paths α H (A.pair.strong y β) δ γ := by
  have hS := S.width_pos
  have hw := ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp counting |>.const_mul_atTop hS).eventually_ge_atTop (4*(S.supportExponent+1))
  have he := A.pair.currency
  have hr := late_cubic (64 * top G S * U)
  filter_upwards [Real.tendsto_log_atTop.eventually (WilsonStartup.Timing.cut S.clip),counting.eventually_ge_atTop 2,
    hw, (tendsto_atTop_add_const_right _ c tendsto_id).eventually he, hr, (similar_gap_power ((11:ℝ)/5)) 2 one_lt_two, just_near c,
    eventually_gt_atTop (1:ℝ),plain.pitched, small_expenses (softCeiling G S U) c] with x hCut hB hW hE hR hN hn hx hPitch hSoft
  intro y H p hh hp hP
  have hy : y = x+c := rfl; have hcx := threshold_aligned x (show 0<x by linarith)
  have hcB : p.B = WilsonStartup.Timing.balls (Real.log x) := hp
  have hs : 0 < (p.B:ℝ) := by exact_mod_cast p.B_pos
  have hxy : 1 < y := hE.1
  refine ⟨fun h => ⟨h,hp ▸ hB,(by rw [hcB,hP,← hcx.2]; exact hCut)⟩,⟨hS,S.slow_selector,(div_le_iff₀ hs).mpr ?_⟩,?_⟩
  · change 4*(S.supportExponent+1) ≤ S.width * ((cover x):ℝ) at hW
    rw [hh.2.2,hp]; linarith
  intro e L hL α θ β ha hb T r δ γ
  have hT := lows e F (x:=x) (θ:=θ) hL hxy hb
  have htwo := hN x y (same x) hn
  change δE x ≤ 2*δE y at htwo
  have h0 : 0 < gap x := gp (by linarith)
  have hx' : 0 ≤ δE x := Real.rpow_nonneg h0.le _
  have hg : gap x ≤ 1 := inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt hx.le)
  have hH := authorized G S
  have hu : top G S * (|α| * p.threshold^3) ≤ δE x/64 := by
    have hb : 64 * top G S * U * p.threshold^3 ≤ δE x := by rw [hP,hcx.1]; exact hR
    nlinarith only [hb, mul_le_mul_of_nonneg_right ha (mul_nonneg (base_nonneg G S).2 (pow_nonneg p.threshold_pos.le 3))]
  have hf : H ≤ p.threshold^2 := by
    have hd : δE x ≤ gap x ^ (2:ℕ) := (Real.rpow_le_rpow_of_exponent_ge h0 hg (by norm_num : (2:ℝ)≤(11:ℝ)/5)).trans_eq (Real.rpow_two _)
    exact le_trans (by dsimp [H]; nlinarith only [mul_le_mul_of_nonneg_right hH.1 hx',hx',hd]) (show gap x ^ (2:ℕ) ≤ p.threshold^2 from
      pow_le_pow_left₀ h0.le (by rw [hP]; exact le_mul_of_one_le_right h0.le hPitch.2.2.1) 2)
  dsimp only at hT
  constructor
  · unfold H T; nlinarith only [mul_le_mul_of_nonneg_right hH.1 hx',hT.1,htwo,hx']
  refine ⟨?_,?_,A.pair.mild y,r,?_,?_⟩
  · unfold δ T; linarith [hT.1,hT.2]
  · rw [table G S hh]; dsimp [H,δ]; linarith only [mul_le_mul_of_nonneg_right hH.2 hx',hu]
  · apply (soft_table G S hh ha (mul_nonneg (credit_pos G S).le hx') hf).trans
    rw [hp,hP]; apply hSoft.trans
    simp only [y,Payments.Pairing.mild,Forecast.pair,pow_zero,Real.rpow_zero,mul_one]
    exact le_mul_of_one_le_left (Real.rpow_pos_of_pos (gp (by rw [← hy]; linarith only [hxy])) _).le (le_max_left ..)
  have hBody : cover x ≤ cover y := Nat.ceil_le_ceil <| pow_le_pow_left₀ (Real.log_pos hx).le (Real.log_le_log (by linarith) (by dsimp [y]; linarith)) 2
  exact hE.2 β hb p.B (hp ▸ hBody)
end YM.AnalyticBridge.VerifiedReset.Time
