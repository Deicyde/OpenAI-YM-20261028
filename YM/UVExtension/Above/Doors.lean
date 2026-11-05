import YM.Extra.WILSON_STARTUP.Clock
import YM.Extra.WILSON_STARTUP.Fast
import YM.UVExtension.Lamppost.Grace

/-!
# Sharper payment on the initial Wilson prescription

Only delays. No dependence on later cutoff, period, or reference b variation.
The window test here gives the margin for our fixed-cards continuation.
-/
noncomputable section
set_option autoImplicit false
namespace YM.UVExtension.Above
open Function Filter RG Wilson Lattice MeasureTheory Precision
open WilsonStartup Start Lamppost Timing
open Real (log exp)
open scoped Matrix.Norms.Frobenius Topology Classical
variable {G : Gauge}

lemma meals (G : Gauge) (A : Stage) {ε : ℝ}(hε:0<ε) : ∀ᶠ s : ℝ in atTop,∀ b : BudgetPoint,
    b.order=A.order → b.power=A.power → b.supportExponent=A.supportExponent → b.threshold=temp s →
      book G b (2*exp s) ≤ ε*normE s := by
  let C := (Fintype.card Signed:ℝ)*Fintype.card PlaqAxes*(exp (A.supportExponent*5^4)*(2*Start.price G A.order A.power))
  have hC : 0<C := by unfold C; have := (constants G A.order A.power).1; positivity
  filter_upwards [small (ε:=1/40) (by norm_num),eventually_ge_atTop (4*(log C - log ε)),eventually_ge_atTop (0:ℝ)] with s h hs hs' b hk hP ha ht
  have hh : book G b (2*exp s) = exp (log C + s + 5*(-(s/2)+(log s)^2)) := by
    simp only [book,item,overhead,ha,hk,hP,ht,temp]
    rw [Real.exp_add (log C + s), Real.exp_add (log C), Real.exp_log hC,show (5:ℝ)=(↑(5:ℕ):ℝ) by norm_num,Real.exp_nat_mul]; unfold C; push_cast; ring
  rw [hh,normE,← Real.exp_log hε,← Real.exp_add,Real.exp_le_exp]
  linarith

lemma bidsK (A:Stage){ε:ℝ}(hε:0<ε): ∀ᶠ s : ℝ in atTop,∀ b : BudgetPoint, b.threshold=temp s→b.B=balls s → b.supportExponent=A.supportExponent→Bid.quote (M s) (exp (quota s)-1)≤ε*normK s:= by
  filter_upwards [loan A.supportExponent,growing.eventually_ge_atTop (2*(1-log ε)),Real.tendsto_log_atTop.eventually_ge_atTop 2] with s h hV hP b hv hb ha
  have H:= (h b hv hb ha).1
  have h₁ : exp (quota s)-1 ≤ 1 := (le_mul_of_one_le_left (sub_nonneg.mpr (Real.one_le_exp (Real.exp_pos _).le)) (one_le_pow₀ (by simp))).trans H.margin
  calc
    _ ≤ exp (-M s) * exp 1 := by unfold Bid.quote; gcongr; exact (sub_le_self _ zero_le_one).trans (Real.exp_le_exp.mpr h₁)
    _ ≤ _ := by
      unfold normK; rw [← Real.exp_log hε,← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
      let v:= exp ((log s)^2/5); have hv : 2*v ≤ M s := by
        have hm : M s = v*exp (4/5*(log s)^2):= by unfold M v; rw [← Real.exp_add]; congr 1; ring
        have h':= Real.add_one_le_exp (4/5*(log s)^2); have ht:2 ≤ exp (4/5*(log s)^2):= by nlinarith
        rw [hm]; exact (mul_comm ..).trans_le (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le)
      change _≤ log ε+ -v; linarith

lemma windowP : ∀ᶠ y in atTop,(stretchB y)*capK ≤ (1/16)*y := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1-98/100)).eventually_ge_atTop (16*capK), eventually_gt_atTop (0:ℝ)] with y he hy
  calc
    _≤ stretchB y*(1/16*y ^ (1-98/100:ℝ)) := mul_le_mul_of_nonneg_left (by linarith only [he]) (Real.rpow_nonneg hy.le _)
    _= _:= by rw [mul_left_comm, stretchB,← Real.rpow_add hy]; norm_num
structure Entry (a : Levels G) (N:ℕ) (ε:ℝ) : Prop where
   cash : book G (a.budget N) (2*a.clock.hatBeta N) ≤ ε*a.clock.allowance N
   ripe : ∃ σ κ γ, Loan (a.budget N) (a.clock.hatBeta N/2) σ κ γ∧ Bid.quote κ (Real.exp γ-1)≤ε*a.clock.forcedAllowance N
   care : (stretchB (a.clock.hatBeta N))*capK ≤ 1/16*(a.clock.hatBeta N)
lemma asking (G : Gauge)(A : Stage){ε:ℝ}(hε:0<ε):∀ᶠ x : ℝ in atTop,∀ a:Levels G,∀ N:ℕ,a.params N=A → a.clock.hatBeta N=x → Entry a N ε:= by
  filter_upwards [Real.tendsto_log_atTop.eventually (meals G A hε),Real.tendsto_log_atTop.eventually (bidsK A hε),Real.tendsto_log_atTop.eventually (loan A.supportExponent),windowP,eventually_gt_atTop (0:ℝ)] with x hE hK hF hp hx a N ha hN
  let b := a.budget N
  have hb : b.B=balls (log x) := congr_arg balls (congr_arg log hN)
  have hp' : (Real.sqrt x)⁻¹ = exp (-(log x / 2)) := by
    rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; congr 2; ring
  have ht : b.threshold = temp (log x) := by
    change (Real.sqrt (a.clock.hatBeta N))⁻¹ * exp _ = _
    unfold temp; rw [hN,hp',Real.exp_add]
  have he : a.clock.allowance N = normE (log x) := by
    unfold Calendar.allowance Calendar.hatCoupling normE; rw [hN,hp',← Real.exp_mul]; congr 1; ring
  have hw : a.clock.forcedAllowance N = normK (log x) := by
    unfold Calendar.forcedAllowance Calendar.monitor normK; rw [hN,← Real.exp_mul]; congr 3; ring
  have hk : b.order=A.order := congr_arg Stage.order ha
  have hP : b.power=A.power := congr_arg Stage.power ha
  have hA : b.supportExponent=A.supportExponent := congr_arg Stage.supportExponent ha
  refine ⟨?_,?_,hN ▸ hp⟩
  · rw [he,hN]; have H:= hE b hk hP hA ht; rw [Real.exp_log hx] at H; exact H
  obtain ⟨q,-⟩ := hF b ht hb hA
  rw [Real.exp_log hx] at q
  rw [hN,hw]; exact ⟨_,_,_,q,hK b ht hb hA⟩

open RG.Supply Push.PriceCompiler Next.Scheduling
variable {s : RG.Supply.Sheet G} {D : Rolls s} {θ: Protection D}
    {T : Delays θ} {a: Levels G} {P: Bar T}{I: Wait P} (hp : Paid I a) {ε:ℝ}

def Fares (ε:ℝ)(T : Delays θ): Prop:= ∀ j x,T.betaEntry j≤ x →∀ a:Levels G,∀ N:ℕ,a.params N=s.profile j→a.clock.hatBeta N=x → Entry a N ε
lemma charts (W:Delays θ)(hε:0<ε):∃ W':Delays θ,DelayLe W W'∧ ∀ Y: Delays θ, DelayLe W' Y → Fares ε Y :=by
  obtain ⟨f,-,hf,hF⟩:= collect_upper W.betaEntry _ (fun j=> asking G (s.profile j) hε)
  exact ⟨{W with betaEntry:=f},⟨hf,le_rfl,le_rfl,le_rfl⟩,fun Y hy j x hx=> hF j x ((hy.beta j).trans hx)⟩
include hp
lemma earned (hv:Fares ε T)(hG:G.Simple):∀ N,Entry a N ε:=by
  intro N; apply hv _ _ _ _ N (params_eq hp N) rfl
  cases N with
  | zero=> simpa only [Calendar.hatBeta,Schedule.scale_zero,mul_zero,add_zero,hp.firstZero,hp.bar] using P.ready
  | succ i => exact (hp.pays i).trans (Timing.hat_mono a (Gauge.slopeConstant_pos hG).le i.le_succ)
end YM.UVExtension.Above
