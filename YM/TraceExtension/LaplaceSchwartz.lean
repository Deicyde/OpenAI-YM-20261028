import YM.TraceExtension.LaplaceLimit

/-! Continuity theorem, Schwartz version with a uniform polynomial bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical

lemma integrable_complex {κ : Measure E4} (hk : AllowsLaplace κ) (f : E4 → ℂ)
    (hc : Continuous f) (hp : HasCompactSupport f) : Integrable f κ := by
    have hr := integrable_sensor hk (re ∘ f) (continuous_re.comp hc) (hp.comp_left rfl)
    have hi := integrable_sensor hk (im ∘ f) (continuous_im.comp hc) (hp.comp_left rfl)
    exact (hr.ofReal.add (hi.ofReal.mul_const I)).congr (ae_of_all _ fun x => Complex.re_add_im _)

theorem laplace_compact_complex {ι : Type*} {l : Filter ι} (μ : ι → Measure E4) (ν : Measure E4)
    (hf : ∀ᶠ i in l, AllowsLaplace (μ i)) (hν : AllowsLaplace ν)
    (hx : ∀ (u : inside), Tendsto (fun i => lag (μ i) u univ) l (𝓝 (lag ν u univ)))
    (f : E4 → ℂ) (hc : Continuous f) (hp : HasCompactSupport f) :
    Tendsto (fun i => ∫ p,f p ∂μ i) l (𝓝 (∫ p,f p ∂ν)) := by
    have hr := laplace_compact μ ν hf hν hx (re ∘ f) (continuous_re.comp hc) (hp.comp_left rfl)
    have hi := laplace_compact μ ν hf hν hx (im ∘ f) (continuous_im.comp hc) (hp.comp_left rfl)
    rw [← integral_re_add_im (integrable_complex hν f hc hp)]
    apply ((Complex.continuous_ofReal.continuousAt.tendsto.comp hr).add
             ((Complex.continuous_ofReal.continuousAt.tendsto.comp hi).mul_const I)).congr'
    filter_upwards [hf] with i hk using integral_re_add_im (integrable_complex hk f hc hp)

lemma schwartz_bound (f : Probe E4) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x, ‖f x‖ ≤ C*((1+‖x‖)^k)⁻¹ := by
    let A n := Probe.size n 0 f
    refine ⟨2^k*(A 0+A k),?_,fun x => ?_⟩
    · unfold A Probe.size; positivity
    have he := pow_mul_le_of_le_of_pow_mul_le (k:=0) (l:=k) (f:=‖f x‖) (C₁:=A 0) (C₂:=A k) (norm_nonneg x) (norm_nonneg (f x))
       (by simpa using SchwartzMap.le_seminorm ℂ 0 0 f x)
       (by simpa using SchwartzMap.le_seminorm ℂ k 0 f x)
    simpa [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+‖x‖),Real.rpow_natCast] using he

private lemma tail_integral (μ : Measure E4) (A : ℝ) (k : ℕ)
    (hA : 0 ≤ A) (hw : energyBudget μ A k) :
    (∫ x : E4, ((1+‖x‖)^(k+1))⁻¹ ∂μ) ≤ (ENNReal.ofReal (A*2^k) * (1-(2:ℝ≥0∞)⁻¹)⁻¹).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (by dsimp; positivity))
        ((inverse_integrable hA (balls_energy hw)).1)]
    exact ENNReal.toReal_mono (falling_finite A k).ne (falling hA (balls_energy hw))

lemma temperate_of_energy (μ : Measure E4) {A : ℝ} {k : ℕ} (hA : 0≤A) (hw : energyBudget μ A k) :
    μ.HasTemperateGrowth := by
    refine ⟨k+1,?_⟩
    simp_rw [show ∀ x:E4,(1+‖x‖) ^ (- ((k+1:ℕ):ℝ))=((1+‖x‖)^(k+1))⁻¹ from fun x => by
      rw [Real.rpow_neg (by positivity),Real.rpow_natCast]]
    exact inverse_integrable hA (balls_energy hw)

set_option maxHeartbeats 800000 in
/-- Approximation error *uniform in measures*. No joint smoothness in scale needed. -/
lemma tail_budget (A : ℝ) (k : ℕ) (hA : 0 ≤ A) (f : Probe E4) (ε : ℝ) (he : 0 < ε) :
    ∃ F : E4 → ℂ, Continuous F ∧ HasCompactSupport F ∧
    ∀ μ : Measure E4, AllowsLaplace μ → energyBudget μ A k → dist (∫ x,F x ∂μ) (∫ x,f x ∂μ) < ε := by
    obtain ⟨C,hC,hf⟩ := schwartz_bound f ((k+1)+1)
    let q := (ENNReal.ofReal (A*2^k) * (1-(2:ℝ≥0∞)⁻¹)⁻¹).toReal
    have hq : 0 ≤ q := ENNReal.toReal_nonneg
    let R := 1 + C*q/ε
    have hR : 0<R := add_pos_of_pos_of_nonneg zero_lt_one (by positivity)
    let B : ContDiffBump (0:E4) := ⟨R,R+1,hR,lt_add_one _⟩
    let F : E4 → ℂ := fun x => (B x : ℝ) • f x
    have hc : Continuous F := B.continuous.smul f.continuous
    have hp : HasCompactSupport F := HasCompactSupport.smul_right (f':=⇑f) B.hasCompactSupport
    refine ⟨F,hc,hp,fun μ hL hw => ?_⟩
    haveI := temperate_of_energy μ hA hw
    let Y := fun x:E4 => ((1+‖x‖)^(k+1))⁻¹
    have h (x : E4) : ‖F x-f x‖ ≤ (C/R)*Y x := by
        by_cases ht : ‖x‖≤R
        · have hf : F x=f x := by
             unfold F; rw [B.one_of_mem_closedBall (Metric.mem_closedBall.mpr (by rwa [dist_zero_right])),one_smul]
          rw [hf,sub_self,norm_zero]; dsimp only [Y]; positivity
        have he : R ≤ 1+‖x‖ := by linarith
        have hB : -1 ≤ B x-1 ∧ B x-1 ≤ 1 := by have := B.nonneg (x:=x); have := B.le_one (x:=x); constructor <;> linarith
        calc
          _ = |B x-1| * ‖f x‖ := by rw [← Real.norm_eq_abs,← norm_smul]; simp [F, sub_smul]
          _ ≤ ‖f x‖ := mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr hB)
          _ ≤ _ := (hf x).trans ?_
        rw [pow_succ, mul_inv_rev,← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_eq_mul_inv]; gcongr
    rw [dist_eq_norm, ← integral_sub (integrable_complex hL _ hc hp) f.integrable]
    refine lt_of_le_of_lt (norm_integral_le_of_norm_le ((inverse_integrable hA (balls_energy hw)).const_mul (C/R)) (ae_of_all _ fun x => h x)) ?_
    rw [integral_const_mul]; apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (tail_integral μ A k hA hw) (show 0≤C/R by positivity))
    change C/R*q < _; rw [div_mul_eq_mul_div,div_lt_iff₀ hR]
    unfold R; rw [mul_add,mul_one,mul_div_cancel₀ _ he.ne']; linarith only [he]

theorem laplace_schwartz {ι : Type*} {l : Filter ι} (μ : ι → Measure E4) (ν : Measure E4)
    (hf : ∀ᶠ i in l, AllowsLaplace (μ i)) (hν : AllowsLaplace ν)
    (hx : ∀ (u : inside), Tendsto (fun i => lag (μ i) u univ) l (𝓝 (lag ν u univ)))
    (A : ℝ) (k : ℕ) (hA : 0 ≤ A) (hs : energyBudget ν A k) (hw : ∀ᶠ i in l, energyBudget (μ i) A k)
    (f : Probe E4) : Tendsto (fun i => ∫ x,f x ∂μ i) l (𝓝 (∫ x,f x ∂ν)) := by
    apply Metric.tendsto_nhds.mpr; intro ε he
    obtain ⟨F,hc,hp,h⟩ := tail_budget A k hA f (ε/3) (by positivity)
    filter_upwards [hf,hw,Metric.tendsto_nhds.mp (laplace_compact_complex μ ν hf hν hx F hc hp) (ε/3) (by positivity)] with i hF hS hE
    have hu := h (μ i) hF hS; rw [dist_comm] at hu
    apply lt_of_le_of_lt (dist_triangle4 _ (∫ x,F x ∂μ i) (∫ x,F x ∂ν) _)
    linarith [h ν hν hs]
end YM.TraceExtension
