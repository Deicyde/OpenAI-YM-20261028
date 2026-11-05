import YM.Extra.WILSON_STARTUP.Clock
import YM.Further.STRONG_STARTUP_CREDIT.Singles


set_option warningAsError false

/-!
# Extra support *and* stronger M² forcing, numerically

M(s) = monitor = called p_m in E (not B_m!), s = log hatBeta. Clips,
stage and every added finite reserve fixed before L. Work for β even
down to ONE QUARTER of hatBeta in the stronger K and E estimates used
here. No rebuilding the Calendar or threshold for that enlarged payment;
β in the representation doesn't determine the threshold.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.StrongStartup
open Filter Function RG Wilson Lattice WilsonStartup WilsonStartup.Start WilsonStartup.Timing
open Real (log exp)
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge}

/-- Any prepriced extra exponent. Request `δ ≥ 1` (or 8 etc)
when both E and K need this margin. -/
def stretch (b : BudgetPoint) (δ : ℝ) (hδ : 0 ≤ δ) : BudgetPoint :=
  { b with supportExponent := b.supportExponent + δ, exponent_pos := add_pos_of_pos_of_nonneg b.exponent_pos hδ }

def stretchedStage (A : Stage) (δ : ℝ) (hδ : 0 ≤ δ) : Stage :=
  { A with supportExponent := A.supportExponent + δ, price_pos := add_pos_of_pos_of_nonneg A.price_pos hδ }

/-- E-grade small exponential scale paid at the startup K. Same M²
power as in the text, even pre-L rate here (only for THIS startup).
-/
def seedRate : ℝ := share/128
lemma seedRate_pos : 0 < seedRate := div_pos share_pos (by norm_num)
def depth (s : ℝ) := seedRate * M s ^ 2
def grant (A : Levels G) (N : ℕ) := exp (-(seedRate * (A.clock.monitor N)^2))

lemma deep (a : ℝ) : ∀ᶠ s in atTop, exp (-depth s) ≤ normK s ∧
    ∀ b : BudgetPoint, b.threshold=temp s → b.B=balls s → b.supportExponent=a →
    Loan b (exp s/4) (M s) (depth s) (quota s) ∧ Bid.quote (depth s) (exp (quota s)-1) ≤ normK s := by
  filter_upwards [Timing.loan a, Timing.growing.eventually_ge_atTop (1/seedRate)] with s he hM
  have hr := seedRate_pos
  have hm : 0 < M s := Real.exp_pos _
  have hd : M s ≤ depth s := by
    rw [div_le_iff₀ hr] at hM
    unfold depth; nlinarith
  have hp := sq_nonneg (log s)
  refine ⟨?_,fun b hb hx hy => ?_⟩
  · apply Real.exp_le_exp.mpr (neg_le_neg _)
    exact le_trans (b:=M s) (Real.exp_le_exp.mpr (by linarith)) hd
  obtain ⟨hh,hq⟩ := he b hb hx hy
  constructor
  · refine ⟨by positivity, hm.le.trans hd,?_,hh.packets,hh.margin⟩
    have hf : exp s * (temp s)^2 = (M s)^2 := by
      unfold temp M; rw [← Real.exp_nat_mul, ← Real.exp_add,← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc
      _ ≤ depth s + depth s := add_le_add_right hd _
      _ = exp s/4 * gain b := by unfold gain depth seedRate; rw [hb,← hf]; ring
  refine le_trans ?_ hq
  have hz := sub_nonneg.mpr (Real.one_le_exp (sub_nonneg.mpr (Real.one_le_exp hh.packets.gamma)))
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hd)) hz

/-- These are purely numerical tests on a calendar. Issued BEFORE
commissioning the levels/histories. Some bounds are deliberately redundant
so subsequent consumers can use the existing certificates.
-/
structure Escrow (A : Levels G) (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) : Prop where
  old : Allows A N
  income : book G (stretch (A.budget N) δ hδ) (2*A.clock.hatBeta N) ≤ A.clock.allowance N
  loan : let s := log (A.clock.hatBeta N)
    Loan (stretch (A.budget N) δ hδ) (A.clock.hatBeta N / 4) (M s) (depth s) (quota s)
  quote : let s := log (A.clock.hatBeta N)
    Bid.quote (depth s) (exp (quota s)-1) ≤ A.clock.forcedAllowance N
  cheaper : grant A N ≤ A.clock.forcedAllowance N

theorem preReserve (G : Gauge) (A : Stage) (δ : ℝ) (hδ : 0 ≤ δ) (hc : A.clip.direct ≤ 1) :
    ∀ᶠ x : ℝ in atTop, ∀ a : Levels G, ∀ N, a.params N=A → a.clock.hatBeta N=x → Escrow a N δ hδ := by
  let H := stretchedStage A δ hδ
  filter_upwards [Real.tendsto_log_atTop.eventually (Timing.afford G H),
    Real.tendsto_log_atTop.eventually (deep H.supportExponent), Timing.enough G A hc,eventually_gt_atTop (0:ℝ)]
    with x hx hd ho her a N hA hN
  let b := stretch (a.budget N) δ hδ
  have hb : b.B=balls (log x) := congr_arg (balls ∘ log) hN
  have hp : (Real.sqrt x)⁻¹ = exp (-(log x / 2)) := by
    rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos her]; congr 2; ring
  have ht : b.threshold=temp (log x) := by
    change (Real.sqrt (a.clock.hatBeta N))⁻¹ * exp _ = _
    unfold temp; rw [hN,hp,Real.exp_add]
  have he : a.clock.allowance N = normE (log x) := by
    unfold Calendar.allowance Calendar.hatCoupling normE; rw [hN,hp,← Real.exp_mul]; congr 1; ring
  have hw : a.clock.forcedAllowance N = normK (log x) := by
    unfold Calendar.forcedAllowance Calendar.monitor normK; rw [hN,← Real.exp_mul]; congr 3; ring
  have HK : b.order=A.order := congr_arg Stage.order hA
  have HP : b.power=A.power := congr_arg Stage.power hA
  have HE : b.supportExponent=H.supportExponent := congr_arg (fun i : Stage => i.supportExponent+δ) hA
  refine ⟨ho a N hA hN, ?_, ?_, ?_,?_⟩
  · rw [he,hN]; simpa only [Real.exp_log her] using hx b HK HP HE ht
  · dsimp only; rw [hN]; simpa only [Real.exp_log her] using (hd.2 b ht hb HE).1
  · dsimp only; rw [hN,hw]; exact (hd.2 b ht hb HE).2
  unfold grant Calendar.monitor; rw [hw,hN]; exact hd.1

variable {A : Levels G} {n : Side} {N : ℕ} {c : Clip} {b : BudgetPoint} {δ κ v : ℝ} {hδ : 0 ≤ δ}
open Ovens Ovens.Pipes RG.Shoot



/-- Explicit k across whole band. Computed from strengthened top receipt,
actual evaluation at ALL U with address predicates intact. Tested through δ+1.
No accumulating the extra power on successive steps from this isolated-
startup argument. -/
def topPrice (A : Levels G) (N p : ℕ) (i : ℕ) : ℝ := let s := log (A.clock.hatBeta N)
    kCoin G (A.S.side N p) (A.budget N) (M s) (depth s) i













end YM.Further.StrongStartup
