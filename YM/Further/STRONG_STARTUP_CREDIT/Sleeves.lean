import YM.Further.STRONG_STARTUP_CREDIT.Reserve



set_option warningAsError false

/-!
# Extra startup payments ready for the first use of the shared-tag density

There is NO block-likelihood multiplier in Thick itself; the top density is
exactly the unnormalized Wilson density. Already the first push will use the
shared-tag averaging prescription. Here price also the supremum charge
of output *local* noise observations on a chosen sleeve: can keep the
M² exponent even when the K is accompanied by all those sharp-bond
factors. Bounds on the FULL joint density then have to either retain the
untouched factors (with the SAME TAGS) or pay a volume cost. We're
not asserting locality/factorization of an observed ratio (and our
sleeve is NOT defining a new species-support or testing connectivity in
the joint density). Entries are paid in the original currency. Doesn't
already estimate new-address majorants needed in Raw at m! Analyses that
actually reassign addresses must also charge the full dependency surface
with its tag, path, flag and sector stencils, not priced by saying the noise
observation bound was on a few edges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.StrongStartup
open Function Filter Finset RG RG.Shoot Lattice Wilson WilsonStartup WilsonStartup.Start WilsonStartup.Timing
  
open Real (log exp)
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {b : BudgetPoint} {f c : Side} {d : Clip}









def rimPrice (B r : ℕ) := (2*B+2*B+1)^4 * (r*B+r*B+1)^4 * (2*Fintype.card Axis)





def shellBound (G : Gauge) (K : KernelChoices) (x : ℝ) :=
  K.penalty / 2 + Module.finrank ℝ G.Mat * log (4*(1+2*x))

def BondFuel (A : Levels G) (N r : ℕ) := let b := A.budget N; let x := A.clock.hatBeta N
  (rimPrice b.B r:ℝ) * shellBound G A.clock.kernel x ≤ x/4 * gain b

lemma sleeve_pre (r : ℕ) (K : KernelChoices) (G : Gauge) : ∀ᶠ s in atTop, ∀ b : BudgetPoint, b.threshold=temp s → b.B=balls s →
    (rimPrice b.B r:ℝ) * shellBound G K (exp s) ≤ exp s /4 * gain b := by
  let d := (Module.finrank ℝ G.Mat:ℝ)
  let q := K.penalty/2
  let A := q+d*(log 12+1)
  let C := (9:ℝ)^4 * (4*r+1)^4 * (2*Fintype.card Axis)
  have hc : 0 ≤ C := by unfold C; positivity
  have hq : 0 ≤ q := by unfold q; have := K.penalty_pos; positivity
  have hp : 0 ≤ log 12 := Real.log_nonneg (by norm_num)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hA : 0 ≤ A := by unfold A; positivity
  filter_upwards [hard_growth 17, growing.eventually_ge_atTop (C*A/seedRate), eventually_ge_atTop (1:ℝ)] with s he hB hs b ht hb
  have hS : shellBound G K (exp s) ≤ A*s := by
    have hz : 1 ≤ exp s := Real.one_le_exp (by linarith)
    have hh : log (4*(1+2*exp s)) ≤ log 12+s := by
      have hh := Real.log_le_log (x:=4*(1+2*exp s)) (y:=12*exp s) (by positivity) (by linarith)
      rwa [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)),Real.log_exp] at hh
    change q+d*log _ ≤ _
    calc
      _ ≤ q+d*(log 12+s) := by gcongr
      _ ≤ _ := by unfold A; nlinarith [mul_le_mul_of_nonneg_right hs (add_nonneg hq (mul_nonneg hd hp))]
  have hR : (rimPrice b.B r:ℝ) ≤ C * s^16 := by
    have hr : (b.B:ℝ) ≤ 2*s^2 := by
      rw [hb]; refine (Nat.ceil_lt_add_one (sq_nonneg s)).le.trans ?_; nlinarith
    unfold rimPrice C; push_cast
    rw [show (9^4 * (4 * (r:ℝ)+1)^4 * (2*(Fintype.card Axis:ℝ))) * s^16 =
             (9*s^2)^4*((4*r+1)*s^2)^4*(2*(Fintype.card Axis:ℝ)) by ring]
    have h1 : 2*(b.B:ℝ) + 2*b.B + 1 ≤ 9*s^2 := by linarith [show 1 ≤ s^2 by nlinarith]
    have h2 : (r:ℝ)*b.B + r*b.B + (1:ℝ) ≤ (4*r+1)*s^2 := by
      have hh := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ (r:ℝ))
      nlinarith
    gcongr (?_) ^4 * (?_)^4 * _
  have hsM : s^17 ≤ M s := he.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (log s)]))
  have hh : C*A ≤ M s * seedRate := (div_le_iff₀ seedRate_pos).mp hB
  have hf : exp s * (temp s)^2 = (M s)^2 := by
    unfold temp M; rw [← Real.exp_nat_mul, ← Real.exp_add,← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hr := seedRate_pos
  calc
    _ ≤ (C*s^16) * (A*s) := (mul_le_mul_of_nonneg_left hS (by positivity)).trans (mul_le_mul_of_nonneg_right hR (by positivity))
    _ = (C*A)*s^17 := by ring
    _ ≤ (M s*seedRate)*M s := mul_le_mul hh hsM (by positivity) (mul_nonneg (Real.exp_pos _).le hr.le)
    _ ≤ _ := by unfold gain; rw [ht]; unfold seedRate; have := share_pos; nlinarith [sq_nonneg (M s), mul_pos (Real.exp_pos s) (sq_pos_of_pos (Real.exp_pos (-(s/2)+(log s)^2)))]

lemma sleeves (r : ℕ) (K : KernelChoices) (G : Gauge) : ∀ᶠ x in atTop, ∀ A : Levels G, ∀ N,
    A.clock.kernel=K → A.clock.hatBeta N=x → BondFuel A N r := by
  filter_upwards [Real.tendsto_log_atTop.eventually (sleeve_pre r K G), eventually_gt_atTop (0:ℝ)] with x hh hx A N hK hB
  unfold BondFuel; dsimp only; rw [hK,hB]
  have hp : (Real.sqrt x)⁻¹ = exp (-(log x / 2)) := by
    rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; congr 2; ring
  have hb : (A.budget N).B=balls (log x) := congr_arg (balls ∘ log) hB
  have ht : (A.budget N).threshold=temp (log x) := by
    change (Real.sqrt (A.clock.hatBeta N))⁻¹ * exp _ = _
    unfold temp; rw [hB,hp,Real.exp_add]
  simpa only [Real.exp_log hx] using hh (A.budget N) ht hb
end YM.Further.StrongStartup
