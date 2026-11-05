import YM.Push.LOCAL_SPLITTING.Initial

/-! Numerical delay for the local merger and initial conversion, at fixed
budget choices. Does not verify all the promises of any RG schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Filter RG Source Labels
open scoped Topology BigOperators
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}

private def mon (x : ℝ) := Real.exp ((Real.log (Real.log x))^2)
private def gasRate (x : ℝ) := Real.exp (- ((mon x) ^ ((1 : ℝ)/5)))

theorem allowance_pos (H : Calendar G) (m : ℕ) : 0 < H.forcedAllowance m := Real.exp_pos _

private theorem gasRate_le (x : ℝ) : gasRate x ≤ 1 := by
  unfold gasRate; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by unfold mon; positivity))

private theorem power_delay (C : ℝ) (k : ℕ) : ∀ᶠ x : ℝ in atTop, C*x^k*Real.sqrt (gasRate x) ≤ 1 := by
  have h := Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1:ℝ),(h.comp h).eventually_ge_atTop 10, h.eventually_ge_atTop (2*((k:ℝ)+|C|)+1)] with x hx he hL
  dsimp only [Function.comp_apply] at he
  let l := Real.log x; let L := Real.log l
  have hp : 0 < l := Real.log_pos hx
  have hy : l^2 ≤ (mon x)^((1:ℝ)/5) := by
    rw [mon,← Real.exp_mul, ← show Real.exp (2*Real.log (Real.log x)) = l^2 from (Real.exp_nat_mul L 2).trans (by simp [L, Real.exp_log hp])]
    apply Real.exp_le_exp.mpr; nlinarith
  rw [gasRate, Real.sqrt_eq_rpow,← Real.exp_mul, ← Real.exp_log (zero_lt_one.trans hx), ← Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hx),mul_assoc, ← Real.exp_add]
  calc
    _ ≤ Real.exp |C| * Real.exp (-|C|) := mul_le_mul ((le_abs_self _).trans (by linarith [Real.add_one_le_exp |C|])) (Real.exp_le_exp.mpr (by dsimp only [l] at hp hy; nlinarith [abs_nonneg C])) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]

private def width (x : ℝ) := ((((Nat.ceil ((Real.log x)^2))+(Nat.ceil ((Real.log x)^2))+1)^4 : ℕ):ℝ)

private theorem width_delay : ∀ᶠ x : ℝ in atTop, width x * Real.sqrt (gasRate x) ≤ 1 := by
  filter_upwards [power_delay (5^4) 8, eventually_gt_atTop (1:ℝ)] with x hh hx
  have hC : ((Nat.ceil ((Real.log x)^2)):ℝ) ≤ 2*x^2 := by
    have := Real.log_pos hx
    nlinarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans hx),Nat.ceil_lt_add_one (sq_nonneg (Real.log x))]
  apply le_trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)) hh
  unfold width; push_cast
  exact (pow_le_pow_left₀ (by positivity) (by nlinarith : _+_+1 ≤ 5*x^2) 4).trans_eq (by ring)

private theorem inv_threshold_le (C : Levels G) (m : ℕ) : (C.budget m).threshold⁻¹ ≤ C.clock.hatBeta m := by
  let x := C.clock.hatBeta m
  have hx : 1 < x := C.fits.delayed m
  have he : 1 ≤ mon x := Real.one_le_exp (sq_nonneg _)
  change ((Real.sqrt x)⁻¹ * mon x)⁻¹ ≤ x
  rw [mul_inv,inv_inv]; exact (mul_le_of_le_one_right (Real.sqrt_nonneg _) (inv_le_one_of_one_le₀ he)).trans (by nlinarith [Real.sq_sqrt (zero_le_one.trans hx.le)])

/-- Threshold sufficient even across levels below a given support-exponent
ceiling. Stage constant chosen without torus side or block ratio. `minSide`,
orders, and general column costs must *also* be funded. No claim that
`Fits` for an arbitrary `Levels` enforces this delay. -/
theorem delay (T : SectionData F) (u : ℝ) : ∃ s : ℝ, ∀ C : Levels G, ∀ m, (C.params m).supportExponent ≤ u → s ≤ C.clock.hatBeta m →
    hitWidth (C.budget m)* Real.sqrt (C.clock.forcedAllowance m) ≤ 1 ∧ BareDelay T (C.budget m) (C.clock.forcedAllowance m) := by
  obtain ⟨s,hs⟩ := eventually_atTop.mp ((width_delay.and (power_delay T.stencil.card 0)).and (power_delay (bareConstant T u) (maxPower F)))
  refine ⟨s,fun C m hm h => ⟨(hs _ h).1.1,?_,?_⟩⟩
  · have he := (hs _ h).1.2
    simp only [pow_zero,mul_one] at he
    have hκ := allowance_pos C.clock m
    exact le_trans (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (x:=C.clock.forcedAllowance m) (y:=gasRate (C.clock.hatBeta m)) (by change _ ≤ C.clock.forcedAllowance m; nlinarith [show C.clock.forcedAllowance m ≤ 1 from gasRate_le _])) (by positivity)) he
  apply le_trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)) (hs _ h).2
  have ht := (full_cost T).choose_spec.1
  have ht' : 0 ≤ fullPrice T := zero_le_one.trans ht
  refine mul_le_mul ?_ (pow_le_pow_left₀ (by positivity [(C.budget m).threshold_pos]) (inv_threshold_le C m) _) (by positivity [(C.budget m).threshold_pos]) (by unfold bareConstant; positivity)
  unfold bareConstant; gcongr; exact hm
end YM.Push.Local
