import YM.TraceExtension.Damping

/-! Polynomial mass bound and explicit seminorm-ready rapid-weight estimate. -/

set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral OS
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace

/-- The sublevel sets are not balls; here even the time slab is controlled. -/
def energyBudget (μ : Measure E4) (A : ℝ) (k : ℕ) := ∀ R : ℝ, 1 ≤ R →
    μ {p | time p ≤ R} ≤ ENNReal.ofReal (A*R^k)

lemma damped_lower (μ : Measure E4) {R : ℝ} {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal (Real.exp (-s*R)) * μ {p | time p ≤ R} ≤ OS.Semigroup.transform timeAxis s μ univ := by
  let U := {p | time p ≤ R}
  have hu : MeasurableSet U := (isClosed_le Mink.clock_cont continuous_const).measurableSet
  let d (p) : ℝ≥0∞ := (OS.Semigroup.descent timeAxis s p)
  change _ * μ U ≤ μ.withDensity d univ
  refine le_trans ?_ (measure_mono (μ := μ.withDensity d) (subset_univ U))
  rw [withDensity_apply _ hu, ← setLIntegral_const]
  apply setLIntegral_mono' hu; intro x hx
  have he : (Real.exp (-s * time x)) = ((OS.Semigroup.descent timeAxis s x : ℝ≥0) : ℝ) := rfl
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-s*time x)) := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr hs)))
    _ = _ := by rw [he,ENNReal.ofReal_coe_nnreal]

variable {G : Gauge} {L : Register G} {S T : Table L} {C : Chamber T timeAxis}
  {F : Waves S} {B : Small S C} {J : StarOp S}

lemma energy_bounded (h : Bid.Hull B F J) (hm : F.Breathes) (v : S.Union) :
    ∃ (A : ℝ) (k : ℕ), 0 ≤ A ∧ energyBudget (spectralMeasure B v) A k := by
  let μ := spectralMeasure B v
  obtain ⟨k,A,hA,hb⟩ := hm 2 (pairV J v)
  refine ⟨A/Real.exp (-2),k,by positivity,fun R hR => ?_⟩
  have hr : 0<R := lt_of_lt_of_le zero_lt_one hR
  let s : ℝ≥0 := ⟨R⁻¹,by positivity⟩
  let ρ := C.flow.ℚmeasure.diagonal (pointState B v s)
  have hp : 0 < s := inv_pos.mpr hr
  have hs : (s:ℝ) ∈ Ioc (0:ℝ) 1 := ⟨hp,inv_le_one_of_one_le₀ hR⟩
  have he := damped_lower μ (R:=R) (s:=2*(s:ℝ)) (by positivity)
  rw [show μ=spectralMeasure B v from rfl,damp h v s hp,show -(2*(s:ℝ))*R = -2 by change -(2 * R⁻¹)*R=-2; field_simp] at he
  have ht : ρ.real univ ≤ A*R^k := by
    have hg : broad (pairH (s:ℝ)) (s:ℝ) := by
        intro i j hj; fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hj (by decide)) | simp
    have hu := hb (pairH s) s hs hg 0
    rw [pair_restricted h v s hp,PiLp.zero_apply,PiLp.zero_apply,sub_zero,charFun_zero] at hu
    change ‖(↑(ρ.real _) : ℂ)‖ ≤ A * (R⁻¹)⁻¹^_ at hu
    simpa [Complex.norm_real, abs_of_nonneg measureReal_nonneg] using hu
  have hf : ρ univ ≤ ENNReal.ofReal (A*R^k) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm.le.trans (ENNReal.ofReal_le_ofReal ht)
  rw [div_mul_eq_mul_div, ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top)).2
  rw [mul_comm]; exact he.trans hf

lemma balls_energy {μ : Measure E4} {A : ℝ} {k : ℕ} (h : energyBudget μ A k) (R : ℝ) (hr : 1 ≤ R) :
    μ (closedBall 0 R) ≤ ENNReal.ofReal (A*R^k) := by
  refine le_trans (measure_mono fun x hx => ?_) (h R hr)
  change time x ≤ R
  rw [mem_closedBall,dist_zero_right] at hx
  exact le_trans (le_abs_self (time x)) ((PiLp.norm_apply_le x timeAxis).trans hx)

section shell
variable {X : Type*} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]

def shell (i : ℕ) := {x : X | 2^i ≤ 1+‖x‖ ∧ 1+‖x‖ ≤ 2^(i+1)}
lemma shell_meas (i : ℕ) : MeasurableSet (shell (X:=X) i) :=
  ((isClosed_le continuous_const (continuous_const.add continuous_norm)).inter
    (isClosed_le (continuous_const.add continuous_norm) continuous_const)).measurableSet
omit [MeasurableSpace X] [BorelSpace X] in
lemma shell_union : (⋃ i, shell (X := X) i)=univ := by
  apply eq_univ_of_forall; intro x
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (1+‖x‖) (show 1<(2:ℝ) by norm_num)
  have he (n : ℕ) (hn : 1+‖x‖ ≤ 2^(n+1)) : ∃ i, x∈shell i := by
    induction n with
    | zero => exact ⟨0,by simp,hn⟩
    | succ n ih =>
      rcases le_total (1+‖x‖) (2^(n+1)) with h|h
      · exact ih h
      exact ⟨n+1,h,hn⟩
  exact mem_iUnion.mpr (he n (hn.le.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _))))

/-- dyadic sum estimate used also for varying measures -/
theorem falling {μ : Measure X} {A : ℝ} {k : ℕ} (hA : 0 ≤ A)
    (hb : ∀ R : ℝ, 1 ≤ R → μ (closedBall 0 R) ≤ ENNReal.ofReal (A*R^k)) :
    ∫⁻ x : X, ENNReal.ofReal (((1+‖x‖)^(k+1))⁻¹) ∂μ ≤
      ENNReal.ofReal (A*2^k) * (1-(2:ℝ≥0∞)⁻¹)⁻¹ := by
  let f (x:X) := ENNReal.ofReal (((1+‖x‖)^(k+1))⁻¹)
  have hu i : ∫⁻ x in shell i, f x ∂μ ≤ ENNReal.ofReal (A*2^k) * (2:ℝ≥0∞)⁻¹^i := by
    let p := (2:ℝ)^i
    have hp : 0<p := by unfold p; positivity
    have h : μ (shell i) ≤ ENNReal.ofReal (A*(2^(i+1):ℝ)^k) :=
      le_trans (measure_mono fun x hx => mem_closedBall.mpr (by
        rw [dist_zero_right]; exact le_trans (le_add_of_nonneg_left (by norm_num : (0:ℝ)≤1)) hx.2))
        (hb _ (one_le_pow₀ (by norm_num)))
    calc
       _ ≤ ∫⁻ _ in shell (X:=X) i, ENNReal.ofReal ((p^(k+1))⁻¹) ∂μ :=
         setLIntegral_mono' (shell_meas i) (fun x hx => ENNReal.ofReal_le_ofReal
           (inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le hx.1 (k+1))))
       _ ≤ _ := by
         rw [setLIntegral_const]
         refine (mul_le_mul_right h _).trans_eq ?_
         rw [← ENNReal.ofReal_mul (by positivity)]
         rw [pow_succ (2:ℝ) i]
         have ht : (p^(k+1))⁻¹ * (A*(p*2)^k) = A*2^k * p⁻¹ := by rw [mul_pow,pow_succ]; field_simp
         change ENNReal.ofReal ((p ^ (k+1))⁻¹ * (A*(p*2)^k)) = _
         rw [ht, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
         simp [p, ENNReal.inv_pow, ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2)]
  change ∫⁻ x, f x ∂μ ≤ _
  calc
    _ = ∫⁻ x in ⋃ i, shell (X:=X) i, f x ∂μ := by simp [shell_union]
    _ ≤ ∑' i, ∫⁻ x in shell i, f x ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' i : ℕ, ENNReal.ofReal (A*2^k) * (2:ℝ≥0∞)⁻¹^i := ENNReal.tsum_le_tsum hu
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

lemma falling_finite (A : ℝ) (k : ℕ) : ENNReal.ofReal (A*2^k) * (1-(2:ℝ≥0∞)⁻¹)⁻¹ < ⊤ := by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    apply ENNReal.inv_lt_top.mpr
    exact tsub_pos_of_lt (by norm_num)

lemma inverse_integrable {μ : Measure X} {A : ℝ} {k : ℕ} (hA : 0 ≤ A)
    (hb : ∀ R : ℝ, 1 ≤ R → μ (closedBall 0 R) ≤ ENNReal.ofReal (A*R^k)) [SecondCountableTopology X] :
    Integrable (fun x : X => ((1+‖x‖)^(k+1))⁻¹) μ := by
  refine ⟨(show Continuous (fun x : X => ((1+‖x‖)^(k+1))⁻¹) from Continuous.inv₀ (by fun_prop) (by intro; positivity)).aestronglyMeasurable,?_⟩
  unfold HasFiniteIntegral
  apply lt_of_le_of_lt _ (falling_finite A k)
  simp_rw [show ∀ x:X, ‖((1+‖x‖)^(k+1))⁻¹‖ₑ=ENNReal.ofReal _ from fun x => Real.enorm_eq_ofReal (by positivity : 0 ≤ ((1+‖x‖)^(k+1))⁻¹)]; exact falling hA hb
end shell

lemma spectral_temperate (h : Bid.Hull B F J) (hm : F.Breathes) (v : S.Union) : (spectralMeasure B v).HasTemperateGrowth := by
    obtain ⟨A,k,hA,hk⟩ := energy_bounded h hm v
    refine ⟨k+1,?_⟩; simp_rw [show ∀ x:E4,(1+‖x‖) ^ (- ((k+1:ℕ):ℝ))=((1+‖x‖)^(k+1))⁻¹ from fun x => by rw [Real.rpow_neg (by positivity),Real.rpow_natCast]]
    exact inverse_integrable hA (balls_energy hk)
end YM.TraceExtension
