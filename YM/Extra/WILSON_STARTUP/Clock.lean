import YM.Extra.WILSON_STARTUP.Cake

/-!
# Sufficient per-stage delays before realizing the schedule

All asymptotics for startup asks only. s = log hatBeta (not the RG scale).
Stage fixed, delays upgradeable, no dependence on N,p or accumulated number
of steps in that stage. No assertion that continuation/source/spectral asks
have been purchased with these same choices.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Timing
open Function Filter RG Wilson Lattice Design Work Start
open Real (log exp)
open scoped Matrix.Norms.Frobenius Topology
variable {G : Gauge}

def M (s : ℝ) := exp ((log s)^2)
def temp (s : ℝ) := exp (-(s/2)+(log s)^2)
def normE (s : ℝ) := exp (-(11/10)*s)
def normK (s : ℝ) := exp (-exp ((log s)^2/5))
def balls (s : ℝ) := Nat.ceil (s^2)
def quota (s : ℝ) := exp (-M s/2)

lemma small {ε : ℝ} (he : 0<ε) : ∀ᶠ s in atTop,(log s)^2 ≤ ε*s := by
  filter_upwards [Real.isLittleO_pow_log_id_atTop (n:=2) |>.def he, eventually_ge_atTop (0:ℝ)] with s hs h
  simpa only [Real.norm_of_nonneg (sq_nonneg _),id_eq,Real.norm_of_nonneg h] using hs

lemma growing : Tendsto M atTop atTop := Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (n:=2) (by omega)).comp Real.tendsto_log_atTop)
lemma nballs : Tendsto balls atTop atTop := tendsto_nat_ceil_atTop.comp (tendsto_pow_atTop (n:=2) (by omega))

lemma shrinking : Tendsto temp atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp (f:=fun s => -(s/2)+(log s)^2) (tendsto_atBot_mono' atTop (f₁ := fun s : ℝ => (-1/4:ℝ)*s) ?_ ?_)
  · filter_upwards [small (ε:=1/4) (by norm_num)] with s h; change -(s/2)+(log s)^2 ≤ _; linarith
  exact tendsto_id.const_mul_atTop_of_neg (by norm_num)

lemma cut (p : Clip) : ∀ᶠ s in atTop, 2 ≤ temp s * exp (((balls s - 2 : ℕ) : ℝ)/p.relaxation) := by
  filter_upwards [nballs.eventually_ge_atTop 2, eventually_ge_atTop (2*p.relaxation),eventually_ge_atTop (log 2+2/p.relaxation)] with s h hs h'
  have he : s^2 ≤ (balls s:ℝ) := Nat.le_ceil _
  have hp := p.radius_pos
  have hx : 2*s ≤ (balls s:ℝ)/p.relaxation := (le_div_iff₀ hp).mpr (by nlinarith)
  have hs0 : 0 ≤ s := by linarith
  rw [temp, ← Real.exp_add,← Real.log_le_iff_le_exp (by norm_num), Nat.cast_sub h]; push_cast; rw [sub_div]
  linarith [sq_nonneg (log s)]

lemma afford (G : Gauge) (A : Stage) : ∀ᶠ s : ℝ in atTop,∀ b : BudgetPoint,
    b.order=A.order → b.power=A.power → b.supportExponent=A.supportExponent → b.threshold=temp s →
      book G b (2*exp s) ≤ normE s := by
  let C := (Fintype.card Signed:ℝ)*Fintype.card PlaqAxes*(exp (A.supportExponent*5^4)*(2*Start.price G A.order A.power))
  have hC : 0<C := by unfold C; have := (constants G A.order A.power).1; positivity
  filter_upwards [small (ε:=1/40) (by norm_num),eventually_ge_atTop (4*log C)] with s h hs b hk hP ha ht
  have hh : book G b (2*exp s) = exp (log C + s + 5*(-(s/2)+(log s)^2)) := by
    simp only [book,item,overhead,ha,hk,hP,ht,temp]
    rw [Real.exp_add (log C + s), Real.exp_add (log C), Real.exp_log hC,show (5:ℝ)=(↑(5:ℕ):ℝ) by norm_num,Real.exp_nat_mul]; unfold C; push_cast; ring
  rw [hh,normE,Real.exp_le_exp]; linarith [sq_nonneg (log s)]

lemma hard_growth (N : ℕ) : ∀ᶠ s : ℝ in atTop, s^N ≤ exp ((log s)^2/5) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop ((5:ℝ)*N),eventually_gt_atTop (0:ℝ)] with s hs h
  have hN : 0 ≤ (N : ℝ) := by positivity
  rw [show s^N = exp ((N:ℝ)* log s) by rw [Real.exp_nat_mul,Real.exp_log h],Real.exp_le_exp]; nlinarith

lemma many : ∀ᶠ s in atTop, ((2*balls s+2*balls s+1:ℕ):ℝ)^4 ≤ M s / 4 := by
  filter_upwards [hard_growth 16,eventually_ge_atTop (4:ℝ)] with s hs hx
  have hB : (balls s : ℝ) ≤ s^2+1 := (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have hM : s^16 ≤ M s := hs.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (log s)]))
  have he : 2 * (((2*balls s+2*balls s+1:ℕ):ℝ)) ≤ s^4 := by
    push_cast; nlinarith [sq_nonneg (s^2-8)]
  calc
    _ ≤ (s^4/2)^4 := by gcongr; linarith
    _ = s^16/16 := by ring
    _ ≤ _ := by have hm : 0 < M s := Real.exp_pos _; linarith

lemma loan (a : ℝ) : ∀ᶠ s in atTop, ∀ b : BudgetPoint, b.threshold=temp s → b.B=balls s → b.supportExponent=a →
    Loan b (exp s/2) (M s) (M s) (quota s) ∧ Bid.quote (M s) (exp (quota s)-1) ≤ normK s := by
  filter_upwards [many, growing.eventually_ge_atTop (64/share),growing.eventually_ge_atTop (4*((a+1+1)*5^4)),
      Real.tendsto_log_atTop.eventually_ge_atTop 3] with s hM hh ha hs b ht hb he
  have hm : 0 < M s := Real.exp_pos _
  have hq : 0 ≤ quota s := (Real.exp_pos _).le
  have hw : exp (quota s)-1 ≤ 2*quota s := by
    refine (le_abs_self _).trans ((Real.abs_exp_sub_one_le ?_).trans_eq (by rw [abs_of_nonneg hq]))
    rw [abs_of_nonneg hq]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hc : ((b.B+b.B+1:ℕ):ℝ)^4 ≤ M s/4 := le_trans ?_ hM
  · have hj := Real.add_one_le_exp (M s/2)
    have hz : M s / 4 * (2*quota s) ≤ 1 := by
      rw [quota,neg_div,Real.exp_neg]; field_simp; linarith
    have hl := (mul_le_mul hc hw (sub_nonneg.mpr (Real.one_le_exp hq)) (by positivity)).trans hz
    refine ⟨⟨by positivity,hm.le,?_,⟨by have := b.exponent_pos; positivity,?_,?_⟩,hl⟩,?_⟩
    · unfold gain; rw [ht]
      have hf : exp s * (temp s)^2 = (M s)^2 := by
        unfold temp M; rw [← Real.exp_nat_mul, ← Real.exp_add,← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [div_le_iff₀ share_pos] at hh
      calc
        _ ≤ (M s)^2*(share/32) := by nlinarith
        _ = _ := by rw [← hf]; ring
    · exact (mul_le_mul hc (by linarith) hq (by positivity)).trans hz
    · rw [he,hb,quota, show -M s / 2 = M s/4 + (M s/4 - M s) by ring,Real.exp_add]
      gcongr
      · exact hM.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
      · linarith
    unfold Bid.quote normK
    have h₁ : exp (quota s)-1 ≤ 1 := (le_mul_of_one_le_left (sub_nonneg.mpr (Real.one_le_exp hq)) (one_le_pow₀ (by simp))).trans hl
    calc
      _ ≤ exp (-M s) * exp 1 := by gcongr; exact (sub_le_self _ zero_le_one).trans (Real.exp_le_exp.mpr h₁)
      _ ≤ _ := by
        rw [← Real.exp_add,Real.exp_le_exp,M]
        have ht := Real.add_one_le_exp (4/5*(log s)^2)
        have hj : 1 ≤ exp ((log s)^2/5) := Real.one_le_exp (by positivity)
        rw [show exp ((log s)^2)=exp ((log s)^2/5)*exp (4/5*(log s)^2) by rw [← Real.exp_add]; congr 1; ring]
        nlinarith
  rw [hb]; gcongr <;> omega

lemma enough (G : Gauge) (A : Stage) (h : A.clip.direct ≤ 1) : ∀ᶠ x : ℝ in atTop, ∀ a : Levels G, ∀ N,
    a.params N=A → a.clock.hatBeta N=x → Allows a N := by
  filter_upwards [Real.tendsto_log_atTop.eventually (cut A.clip),
    Real.tendsto_log_atTop.eventually (shrinking.eventually (ge_mem_nhds (constants G A.order A.power).2.1)),
    Real.tendsto_log_atTop.eventually (afford G A),Real.tendsto_log_atTop.eventually (loan A.supportExponent),
    Real.tendsto_log_atTop.eventually (nballs.eventually_ge_atTop 2),eventually_gt_atTop (0:ℝ)] with x h₁ h₂ h₃ h₄ h₅ hx a N ha hN
  let b := a.budget N
  have hb : b.B=balls (log x) := congr_arg balls (congr_arg log hN)
  have hp : (Real.sqrt x)⁻¹ = exp (-(log x / 2)) := by
    rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; congr 2; ring
  have ht : b.threshold = temp (log x) := by
    change (Real.sqrt (a.clock.hatBeta N))⁻¹ * exp _ = _
    unfold temp; rw [hN,hp,Real.exp_add]
  have he : a.clock.allowance N = normE (log x) := by
    unfold Calendar.allowance Calendar.hatCoupling normE; rw [hN,hp,← Real.exp_mul]; congr 1; ring
  have hw : a.clock.forcedAllowance N = normK (log x) := by
    unfold Calendar.forcedAllowance Calendar.monitor normK; rw [hN,← Real.exp_mul]; congr 3; ring
  have hk : b.order=A.order := congr_arg Stage.order ha
  have hP : b.power=A.power := congr_arg Stage.power ha
  have hE : b.supportExponent=A.supportExponent := congr_arg Stage.supportExponent ha
  refine ⟨⟨ha ▸ h,hb ▸ h₅,?_⟩, ?_, ?_,?_⟩
  · change 2 ≤ b.threshold*_ ; rw [ht, show (a.budget N).B=b.B from rfl,hb,ha]; exact h₁
  · rw [ha]; exact ht ▸ h₂
  · rw [he,hN,← Real.exp_log hx]; simpa using h₃ b hk hP hE ht
  obtain ⟨q,r⟩ := h₄ b ht hb hE
  rw [Real.exp_log hx] at q
  rw [hN,hw]; exact ⟨_,_,_,q,r⟩
end YM.WilsonStartup.Timing
