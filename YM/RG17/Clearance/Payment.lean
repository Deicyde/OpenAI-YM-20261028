import YM.FullVolume.Rise.Lemon
import YM.RG17.Clearance.Trial

/-!
 # Room for amputation estimates

 Post-L, before Bar/Wait and constructors. The post-L rate needs a schedule gate to exploit
 the actual Drifter/Chord bounds on the entire step index set, not just at fixed stage. We
 separate the purchase in this file. Keep room starting at N also; the operation does not
 require at least one block after Wilson startup. Startup proof uses the actual Timing Loan
 with an improved budget *after* buying it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.ClearanceR
open Function Filter Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Jams Apse Chord Tent
open Real (exp log)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G : Gauge}

section money
variable {u : Supply.Sheet G} {D : Rolls u} (P : PostCost D) (a : Levels G)

def bill (z : ℝ) : ℝ := exp (-(exp ((log (log z))^2/5)))

theorem availability (a : Levels G) (m : ℕ) :
    a.clock.forcedAllowance m = bill (a.clock.hatBeta m) := by
  unfold bill Calendar.forcedAllowance Calendar.monitor; rw [← Real.exp_mul]; congr 3; ring

theorem high_monotone {x y : ℝ} (hx : 1 ≤ log x) (hp : 0 < x) (h : x ≤ y) :
    exp ((log (log x))^2) ≤ exp ((log (log y))^2) := by
  have hi : log x ≤ log y := Real.log_le_log hp h
  have hK := Real.log_le_log (zero_lt_one.trans_le hx) hi
  exact Real.exp_monotone (pow_le_pow_left₀ (Real.log_nonneg hx) hK _)

theorem down_bill {x y : ℝ} (hx : 1 ≤ log x) (hp : 0 < x) (h : x ≤ y) : bill y ≤ bill x := by
  have hi := Real.exp_le_exp.mp (high_monotone hx hp h)
  unfold bill
  exact Real.exp_monotone (neg_le_neg (Real.exp_monotone (div_le_div_of_nonneg_right hi (by norm_num))))

lemma hard_room (q : ℝ) (hq : 0 < q) : ∀ᶠ x : ℝ in atTop, ∀ y ≥ x,
    exp (-q* (exp ((log (log y))^2))^2) ≤ (bill x)^2 := by
  filter_upwards [eventually_gt_atTop (0:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ),
    (Timing.growing.comp Real.tendsto_log_atTop).eventually_ge_atTop (2/q)] with x hp hx hh y hy
  let M := exp ((log (log x))^2)
  have hh : 2/q ≤ M := hh
  have ht : 0 ≤ M := Real.exp_nonneg _
  have hi := high_monotone hx hp hy
  have hs : exp ((log (log x))^2/5) ≤ M := Real.exp_monotone
    (by nlinarith only [sq_nonneg (log (log x))])
  have he : 2 ≤ M*q := (div_le_iff₀ hq).1 hh
  unfold bill; rw [← Real.exp_nat_mul (-exp _) 2, Real.exp_le_exp]; push_cast; nlinarith only
    [hs, mul_le_mul_of_nonneg_right he ht, mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ ht hi 2) hq.le]

/-- All-level payment, not asserted for arbitrary PostCost/Calendar pair.
  Includes log ≥ 1 needed to accumulate running costs. Keep in numerical-clock data. -/
structure Mine (a : Levels G) (rate : ℕ → ℝ) : Prop where
  late m : 1 ≤ log (a.clock.hatBeta m)
  strong m : exp (-(rate (a.clock.J (m+1)))*(a.clock.monitor (m+1))^2) ≤
    a.clock.forcedAllowance m ^ 2

lemma mine_delay {T : Protection D} (W : Delays T) :
    ∃ V, DelayLe W V ∧ ∀ S, DelayLe V S → ∀ (B : Bar S) (Y : Wait B) (a : Levels G),
      Paid Y a → Mine a P.g := by
  obtain ⟨z,-,he,hx⟩ := collect_upper W.betaEntry _ (fun j=>
    (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)).and (hard_room (P.g j) (P.posG j)))
  refine ⟨{W with betaEntry := z}, ⟨he,le_rfl,le_rfl,le_rfl⟩, fun V hV B Y a h => ?_⟩
  have hi m := hx (a.clock.J (m+1)) (a.clock.hatBeta m) (le_trans (hV.beta _) (h.pays m))
  refine ⟨fun m => (hi m).1, fun m => ?_⟩
  rw [availability]
  apply (hi m).2 (a.clock.hatBeta (m+1)); rw [beta_eq h]; exact le_add_of_nonneg_right
    (Work.E04.shift_nonneg G _)
end money

section seed
open WilsonStartup.Timing

lemma bright_loan (q : ℝ) : ∀ᶠ s : ℝ in atTop, ∀ b : BudgetPoint, b.threshold=Timing.temp s →
    b.B=Timing.balls s → b.supportExponent=q → Start.Loan b (exp s/2) (M s) (M s) (quota s) ∧
    YM.Bid.quote (M s) (exp (quota s)-1) ≤ (normK s)^2 := by
  filter_upwards [Timing.loan q, Real.tendsto_log_atTop.eventually_ge_atTop (4:ℝ)]
    with s h hp b hb hk hQ
  obtain ⟨h,-⟩ := h b hb hk hQ
  refine ⟨h,?_⟩
  unfold YM.Bid.quote normK
  apply le_trans (b:=exp (-M s)*exp 1) (mul_le_mul_of_nonneg_left
    ((sub_le_self _ zero_le_one).trans (Real.exp_monotone (pill h))) (Real.exp_nonneg _))
  rw [← Real.exp_nat_mul,← Real.exp_add,Real.exp_le_exp,M,
    show exp ((log s)^2)=exp ((log s)^2/5)*exp (4/5*(log s)^2) from (by
      rw [← Real.exp_add]; congr 1; ring)]
  push_cast
  have hx : 1 ≤ exp ((log s)^2/5) := Real.one_le_exp (by positivity)
  have hy : 3 ≤ exp (4/5*(log s)^2) := (by
    nlinarith only [hp] : (3:ℝ) ≤ 4/5*(log s)^2+1).trans (Real.add_one_le_exp _)
  linarith only [hx,mul_le_mul_of_nonneg_right hy (zero_le_one.trans hx)]

def Deposit (a : Levels G) (i : ℕ) : Prop :=
    ∃ σ κ γ, Start.Loan (a.budget i) (a.clock.hatBeta i/2) σ κ γ ∧
      YM.Bid.quote κ (exp γ-1) ≤ (a.clock.forcedAllowance i)^2

lemma deposits (G : Gauge) (A : RG.Stage) : ∀ᶠ x in atTop, ∀ (a : Levels G) N,
    a.params N=A → a.clock.hatBeta N=x → Deposit a N := by
  filter_upwards [Real.tendsto_log_atTop.eventually (bright_loan A.supportExponent),
    eventually_gt_atTop (0:ℝ)] with x h hx a N ha hN
  let b := a.budget N
  have hb : b.B=Timing.balls (log x) := congr_arg balls (congr_arg log hN)
  have hF : (Real.sqrt x)⁻¹ = exp (-(log x / 2)) := by
    rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; congr 2; ring
  have ht : b.threshold=Timing.temp (log x) := by
    change (Real.sqrt (a.clock.hatBeta N))⁻¹ * exp _ = _
    unfold Timing.temp; rw [hN,hF,Real.exp_add]
  obtain ⟨hv,hK⟩ := h b ht hb (congr_arg RG.Stage.supportExponent ha)
  rw [Real.exp_log hx] at hv
  unfold Deposit; rw [availability,hN]; exact ⟨_, _, _, hv, hK⟩

variable {v : Supply.Sheet G} {D : Rolls v} {T : Protection D}
lemma deposits_delay (U : Delays T) : ∃ V, DelayLe U V ∧ ∀ W, DelayLe V W →
    ∀ (b : Bar W) (y : Wait b) (a : Levels G), Paid y a → ∀ m, Deposit a m := by
  obtain ⟨z,-,he,hx⟩ := collect_upper U.betaEntry _ (fun j=> deposits G (v.profile j))
  refine ⟨{U with betaEntry := z}, ⟨he,le_rfl,le_rfl,le_rfl⟩, fun V hV b y a h m => ?_⟩
  refine hx (a.clock.J m) (a.clock.hatBeta m) ((hV.beta _).trans ?_) a m (params_eq h m) rfl
  cases m with
  | zero => rw [h.firstZero, ← h.firstOne]; exact h.pays _
  | succ i => exact (h.pays i).trans (by rw [beta_eq h i]; exact le_add_of_nonneg_right (Work.E04.shift_nonneg G _))

variable {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {R : Roost.Factor A}
open WilsonStartup.Start
lemma startup_bill (N n : ℕ) (hp : Start.Allows A.B.a N) (hb : Deposit A.B.a N)
    (β : ℝ) (hx : β ∈ band A.B.a N) :
    (Tent.launch (A:=A) N n β).activities.KBound (A.B.a.budget N) (A.B.a.clock.forcedAllowance N ^2) := by
  let C := A.B.a.params N; let P := A.B.a.budget N
  let B := A.B.a; let S := B.S.side N n
  obtain ⟨σ,κ,γ,hL,hD⟩ := hb
  have ht : P.threshold ≤ Start.threshold G P.order P.power := hp.radius
  have hz : B.clock.hatBeta N/2 ≤ β := hx.1
  have hg : book G P ‖β‖ ≤ B.clock.allowance N := by
    apply le_trans _ hp.income; unfold Start.book Start.overhead;
    have h₁:= item_pos G P
    have ht : ‖β‖ ≤ 2*B.clock.hatBeta N := by
      rw [Real.norm_of_nonneg (hL.slope.trans hz)]; exact hx.2
    gcongr
  have H : Ingredients (Start.dictionary G S) (Start.payload C.clip P G S β) P
      (B.clock.allowance N) (B.clock.forcedAllowance N ^2) :=
    ⟨κ, Real.exp γ - 1, Real.exp γ - 1, digests hp.clip ht hL hz hg, hL.buys hp.clip hz, hD⟩
  exact (H.gates (A.B.kin.path N N) C.clip β 0).boundK
end seed
end YM.PhysicalNext.Repeat.ClearanceR
