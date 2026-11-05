import YM.TraceExtension.WilsonTrace
import YM.TraceExtension.LaplaceSchwartz

/-!
# Tauberian theorem on the log scale

Implications from `EuclideanAsymptotic` to `prop:lsc` item 2 (spectral part,
with general constant A, ratio *positive*-axis convention). Weak tempered
distribution topology, not rates in strong topology. No ordinary function
interpretation on the light cone. No contact assertion.
-/

set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical

/-- scaling factor on two-point trace spectrum -/
def Zlog (r : ℝ) := r⁻¹ ^ 8 * (Real.log r)^2
lemma Zlog_nonneg (r : ℝ) : 0 ≤ Zlog r := by unfold Zlog; positivity
lemma Zlog_pos {r : ℝ} (h : 1<r) : 0 < Zlog r := by unfold Zlog; have hp:=Real.log_pos h; have hr : 0 < r:=zero_lt_one.trans h; positivity

def rescaled (μ : Measure E4) (r : ℝ) : Measure E4 := ENNReal.ofReal (Zlog r) • μ.map (fun x:E4 => r⁻¹ • x)
lemma scaled_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure E4) (r : ℝ) (hr : 0<r) (φ : E4 → V) :
    (∫ p,φ p ∂rescaled μ r)= Zlog r • ∫ p,φ (r⁻¹ • p) ∂μ := by
    unfold rescaled; rw [integral_smul_measure,ENNReal.toReal_ofReal (Zlog_nonneg _)]
    congr 1
    let e : E4 ≃L[ℝ] E4 := ContinuousLinearEquiv.smulLeft (Units.mk0 r⁻¹ (inv_ne_zero hr.ne'))
    exact e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map _
lemma rescaled_invariant (μ : Measure E4) (r : ℝ) (g : Lorentz) (h : μ.map g.act=μ) :
    (rescaled μ r).map g.act = rescaled μ r := by
    let e := fun p:E4 => r⁻¹ • p; have hc : Measurable e := by unfold e; fun_prop
    have hv : g.act ∘ e = e ∘ g.act := by ext1 x; exact map_smul g.act r⁻¹ _
    rw [rescaled, Measure.map_smul, Measure.map_map g.act.continuous.measurable hc,hv, ← Measure.map_map hc g.act.continuous.measurable,h]
lemma rescaled_cone (μ : Measure E4) (r : ℝ) (hr : 0<r) (h : μ coneᶜ=0) : rescaled μ r coneᶜ=0 := by
    unfold rescaled; rw [Measure.smul_apply,Measure.map_apply (by fun_prop) closed_cone.measurableSet.compl]
    rw [show (fun x:E4 => r⁻¹ • x) ⁻¹' coneᶜ=coneᶜ by
        ext x; simp [cone,norm_smul,abs_of_pos hr,hr]]; rw [h, smul_zero]
lemma rescaled_lag (μ : Measure E4) (r s : ℝ) :
    lag (rescaled μ r) (s • basis timeAxis) univ = ENNReal.ofReal (Zlog r) * lag μ ((s/r) • basis timeAxis) univ := by
    unfold lag rescaled; rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]; rw [lintegral_smul_measure, lintegral_map (lagWeight_meas _) (by fun_prop)]
    rw [smul_eq_mul]; congr 1
    apply lintegral_congr; intro x
    rw [ENNReal.coe_inj]; apply Subtype.ext
    change Real.exp _ = Real.exp _; simp only [real_inner_smul_right,real_inner_smul_left]; congr 2; ring

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {F : Spec.Final C f S}
    {μ : Measure E4}

lemma allows_trace (h : TraceSpectrum F μ) : AllowsLaplace μ where
    supports := h.localcone
    accepts u hu := by
        obtain ⟨s,hs,g,rfl⟩ := future hu
        haveI ht := h.damped_mass _ hs
        exact ⟨by rw [lag_invariant μ h.boost,time_lag]; exact measure_lt_top _ _⟩
lemma allows_rescaled (h : TraceSpectrum F μ) (r : ℝ) (hr : 0<r) : AllowsLaplace (rescaled μ r) where
    supports := rescaled_cone _ _ hr h.localcone
    accepts u hu := by
        obtain ⟨s,hs,g,rfl⟩ := future hu
        haveI ht := h.damped_mass _ (div_pos hs hr)
        exact ⟨by rw [lag_invariant _ (fun g => rescaled_invariant _ r g (h.boost g)), rescaled_lag,time_lag]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
lemma allows_cone (A : ℝ) (ha : 0≤ A) : AllowsLaplace (coneMeasure A) where
    supports := coneMeasure_cone A
    accepts u hu := by
        obtain ⟨s,hs,g,rfl⟩ := future hu
        exact ⟨by rw [lag_invariant _ (coneMeasure_invariant A), cone_laplace _ _ ha hs]; exact ENNReal.ofReal_lt_top⟩
lemma lag_time_univ (h : TraceSpectrum F μ) (s : ℝ) (hp : 0 < s) : lag μ (s • basis timeAxis) univ = ENNReal.ofReal (euclidean F s).re := by
    haveI ht := h.damped_mass _ hp
    rw [time_lag, h.laplace _ hp]; exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- For A positive this is the (complex kernel valued) short distance formula at the specified length. -/
def EuclideanAsymptotic (F : Spec.Final C f S) (A : ℝ) : Prop :=
    Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2):ℝ) • euclidean F s) (𝓝[>] 0) (𝓝 (A:ℂ))
lemma reciprocal {A : ℝ} (hf : EuclideanAsymptotic F A) :
    Tendsto (fun r : ℝ => Zlog r * (euclidean F r⁻¹).re) atTop (𝓝 A) := by
    have h : Tendsto _ _ _ := hf.comp (tendsto_inv_atTop_nhdsGT_zero (𝕜:=ℝ))
    simpa only [Zlog,Function.comp_def, inv_inv, real_smul, smul_eq_mul, mul_re, ofReal_re,ofReal_im,zero_mul, sub_zero] using (Complex.continuous_re.continuousAt.tendsto.comp h)
lemma zlog_shift (s : ℝ) (h : 0<s) : Tendsto (fun r => Zlog r / Zlog (r/s)) atTop (𝓝 (s⁻¹ ^ 8)) := by
    have hr : Tendsto (fun r:ℝ => r/s) atTop atTop := Tendsto.atTop_div_const h tendsto_id
    have hv : Tendsto (fun r : ℝ => (Real.log (r/s))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hr)
    have hu := ((hv.const_mul (Real.log s)).const_add 1).pow 2
    convert ((hu.const_mul (s⁻¹ ^ 8)).congr' ?_) using 2
    · simp
    filter_upwards [hr.eventually (eventually_gt_atTop 1),eventually_gt_atTop 0] with r hr hp
    change 1< r/s at hr; unfold Zlog
    have he : Real.log r=Real.log (r/s)+Real.log s := by rw [Real.log_div hp.ne' h.ne']; ring
    have hx := (Real.log_pos hr).ne'
    conv_rhs => lhs; arg 2; rw [he]
    field_simp

lemma transform_limit {A : ℝ} (h : TraceSpectrum F μ) (ha : 0 ≤ A) (ht : EuclideanAsymptotic F A) (u : inside) :
    Tendsto (fun r => lag (rescaled μ r) u univ) atTop (𝓝 (lag (coneMeasure A) u univ)) := by
    obtain ⟨u,hu⟩ := u; obtain ⟨s,hs,g,rfl⟩ := future hu; dsimp only
    simp_rw [lag_invariant _ (coneMeasure_invariant A), cone_laplace _ _ ha hs]
    have hr : Tendsto (fun r:ℝ => r/s) atTop atTop := Tendsto.atTop_div_const hs tendsto_id
    rw [mul_comm A]
    apply (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((zlog_shift s hs).mul ((reciprocal ht).comp hr))).congr'
    filter_upwards [hr.eventually (eventually_gt_atTop 1),eventually_gt_atTop 1] with r hr hp
    have hh : 0 < r := lt_trans zero_lt_one hp
    rw [lag_invariant _ (fun g => rescaled_invariant μ r g (h.boost g)), rescaled_lag,
      lag_time_univ h _ (div_pos hs hh), ← ENNReal.ofReal_mul (Zlog_nonneg _)]
    dsimp only [Function.comp_apply]; change _=(_ : ℝ≥0∞); congr 1
    rw [inv_div]; field_simp [(Zlog_pos hr).ne']

lemma lower_energy {μ : Measure E4} (A R : ℝ) (hr : 1≤R) (h : lag μ (R⁻¹ • basis timeAxis) univ ≤ ENNReal.ofReal A) :
    μ {p | time p≤R} ≤ ENNReal.ofReal (A/Real.exp (-1)) := by
    have hp : 0<R := zero_lt_one.trans_le hr
    have he := damped_lower μ (R:=R) (inv_pos.mpr hp).le
    rw [← time_lag, neg_mul,inv_mul_cancel₀ hp.ne'] at he
    rw [ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top)).2
    rw [mul_comm]; exact he.trans h
lemma cone_budget (A : ℝ) (ha : 0 ≤ A) : energyBudget (coneMeasure A) (A/Real.exp (-1)) 8 := by
    intro R hr; rw [div_mul_eq_mul_div]; apply lower_energy _ _ hr
    rw [cone_laplace _ _ ha (by have hx : 0 < R := zero_lt_one.trans_le hr; positivity),inv_inv]

lemma rescaled_energy {A : ℝ} (ha : 0≤A) (h : TraceSpectrum F μ) (ht : EuclideanAsymptotic F A) :
    ∃ (C : ℝ), 0 ≤ C ∧ energyBudget (coneMeasure A) C 8 ∧ ∀ᶠ r : ℝ in atTop, energyBudget (rescaled μ r) C 8 := by
    let C := (A+1)/Real.exp (-1)
    refine ⟨C,by unfold C; positivity,fun R hr=> (cone_budget A ha R hr).trans (ENNReal.ofReal_le_ofReal ?_),?_⟩
    · apply mul_le_mul_of_nonneg_right ?_ (by positivity); unfold C; gcongr; linarith
    obtain ⟨D,hD⟩ := eventually_atTop.mp ((reciprocal ht).eventually (ge_mem_nhds (lt_add_one A)))
    filter_upwards [eventually_ge_atTop D,eventually_gt_atTop (1:ℝ)] with r hh hp R hr
    have hz : 0<r := zero_lt_one.trans hp
    have hk : r≤r*R := le_mul_of_one_le_right hz.le hr
    have hx := hD (r*R) (hh.trans hk)
    have hB : 0<R := zero_lt_one.trans_le hr
    unfold C; rw [div_mul_eq_mul_div]; apply lower_energy _ _ hr
    rw [rescaled_lag,lag_time_univ h _ (by positivity), ← ENNReal.ofReal_mul (Zlog_nonneg _)]
    apply ENNReal.ofReal_le_ofReal; rw [show R⁻¹/r=(r*R)⁻¹ by ring]
    have he : Zlog r ≤ Zlog (r*R)* R^8 := by
        have hv : 0 ≤ Real.log r := Real.log_nonneg hp.le
        calc
          _ ≤ r⁻¹^8 * (Real.log (r*R))^2 := by unfold Zlog; gcongr
          _ = _ := by unfold Zlog; field_simp
    have hQ : 0 ≤ (euclidean F (r*R)⁻¹).re := by rw [h.laplace _ (by positivity),ofReal_re]; positivity
    refine (mul_le_mul_of_nonneg_right he hQ).trans ?_
    rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right hx (by positivity)
lemma cone_integral (A : ℝ) (ha : 0 ≤ A) (φ : E4 → ℂ) :
    (∫ p,φ p ∂coneMeasure A)= (A/(1536*Real.pi)) • ∫ p in cone, m p ^2 • φ p := by
    let a := A/(1536*Real.pi); have hp : 0 ≤ a := by unfold a; positivity
    let x (p:E4) : ℝ≥0 := ⟨a*m p^2,by positivity⟩
    have hx : Measurable x := Measurable.subtype_mk (by fun_prop : Measurable fun p:E4 => a*m p^2)
    change (∫ p,φ p ∂(volume.restrict cone).withDensity (fun p => ENNReal.ofReal (a*m p^2))) = a • ∫ p in cone, m p ^2 • φ p
    rw [show (fun p : E4 => ENNReal.ofReal (a*m p^2))=(fun p => (x p:ℝ≥0∞)) from funext (fun p => (@ENNReal.ofReal_coe_nnreal (x p))),
        integral_withDensity_eq_integral_smul hx,← integral_smul]
    congr! 1; ext p; change (a*m p^2) • φ p=a • m p^2 • φ p; rw [smul_smul]
lemma compact_limit {A : ℝ} (ha : 0 ≤ A) (h : TraceSpectrum F μ) (ht : EuclideanAsymptotic F A) (φ : E4 → ℂ)
    (hc : Continuous φ) (hp : HasCompactSupport φ) :
    Tendsto (fun r : ℝ => Zlog r • ∫ p, φ (r⁻¹ • p) ∂μ) atTop (𝓝 ((A/(1536*Real.pi)) • ∫ p in cone,m p ^2 • φ p)) := by
    rw [← cone_integral A ha φ]
    apply (laplace_compact_complex _ _ ((eventually_gt_atTop 0).mono (fun i hi => allows_rescaled h i hi))
      (allows_cone _ ha) (transform_limit h ha ht) φ hc hp).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr using scaled_integral μ _ hr _

lemma schwartz_limit {A : ℝ} (ha : 0≤A) (h : TraceSpectrum F μ) (ht : EuclideanAsymptotic F A) (φ : Probe E4) :
    Tendsto (fun r => ∫ p, φ p ∂rescaled μ r) atTop (𝓝 (∫ p,φ p ∂coneMeasure A)) := by
    obtain ⟨C,hC,hq,hy⟩ := rescaled_energy ha h ht
    exact laplace_schwartz _ _ ((eventually_gt_atTop 0).mono fun i hi => allows_rescaled h i hi) (allows_cone _ ha) (transform_limit h ha ht) C 8 hC hq hy φ
lemma spectral_limit {A : ℝ} (ha : 0≤A) (h : TraceSpectrum F μ) (ht : EuclideanAsymptotic F A) (φ : Probe E4) :
    Tendsto (fun r : ℝ => Zlog r • ∫ p, φ (r⁻¹ • p) ∂μ) atTop (𝓝 ((A/(1536*Real.pi)) • ∫ p in cone, m p ^2 • φ p)) := by
    rw [← cone_integral A ha φ]
    apply (schwartz_limit ha h ht φ).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr using scaled_integral μ _ hr _

section tests
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
/-- Rescale position arguments to inverse length r; junk on r≤0. -/
def condense (r : ℝ) (w : Probe V) : Probe V := if h : 0<r then
    ((↑r:ℂ)^Module.finrank ℝ V) • Probe.along (ContinuousLinearEquiv.smulLeft (Units.mk0 r h.ne')) w
    else w
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma condense_eval (r : ℝ) (hr : 0<r) (w : Probe V) (v : V) : condense r w v = (r^Module.finrank ℝ V : ℝ) • w (r • v) := by
    unfold condense; rw [dif_pos hr]
    change (r:ℂ)^_ • w (r • v)=_; rw [Complex.real_smul]; push_cast; rfl
lemma condense_plus (r : ℝ) (hr : 0<r) (w : Probe V) (v : V) :
    testPlus (condense r w) v=testPlus w (r⁻¹ • v) := by
    rw [testPlus_apply,testPlus_apply]; let d := Module.finrank ℝ V
    have hf : (fun x:V => Probe.plane x v * condense r w x) =
        fun x => (r^d:ℝ) • (Probe.plane (r•x) (r⁻¹•v) * w (r•x)) := by
        ext1 x
        have hh : Probe.plane (r•x) (r⁻¹•v)=Probe.plane x v := by unfold Probe.plane; rw [real_inner_smul_left,real_inner_smul_right,← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul]
        rw [hh,condense_eval r hr,mul_smul_comm]
    rw [hf,integral_smul];
    let f := fun x:V => Probe.plane x (r⁻¹•v)*w x
    change (r^d:ℝ) • (∫ x,f (r•x)) = ∫ x,f x
    rw [Measure.integral_comp_smul_of_nonneg volume f r (hR:=hr.le),smul_smul,mul_inv_cancel₀ (by positivity : (r^d:ℝ) ≠ 0),one_smul]
end tests

lemma wave_scaling (r : ℝ) (hr : 0<r) (w : Joint 2) (p : E4) :
    waveTest (condense r w) p=waveTest w (r⁻¹ • p) := by
    change testPlus (condense r w) (relativeLeg p)=testPlus w (relativeLeg (r⁻¹ • p))
    rw [condense_plus r hr, map_smul relativeLeg]

lemma cone_temperate {A : ℝ} (ha : 0 ≤ A) : (coneMeasure A).HasTemperateGrowth :=
    temperate_of_energy _ (by positivity) (cone_budget A ha)

/-- Tempered distribution convergence in the relative coordinate on every
Schwartz test (including ones straddling or testing on timelike/null regions). -/
theorem relative_limit {A : ℝ} (ha : 0≤A) (h : TraceSpectrum F μ) (ht : EuclideanAsymptotic F A)
    (φ : Probe E4) :
    letI := h.upper
    letI := cone_temperate ha
    Tendsto (fun r => Zlog r • (relative μ) (condense r φ)) atTop (𝓝 ((relative (coneMeasure A)) φ)) := by
    haveI := h.upper; haveI := cone_temperate ha
    apply (schwartz_limit ha h ht (testPlus φ)).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    change _=Zlog r • (relative μ) _
    rw [scaled_integral μ r hr (testPlus φ), relative_apply]
    simp_rw [condense_plus r hr]

/-- Same comparison even with the center coordinate tested jointly. -/
theorem joint_limit {A : ℝ} (ha : 0≤A) (h : TraceSpectrum F μ) (ht : EuclideanAsymptotic F A)
    (φ : Joint 2) :
    Tendsto (fun r => Zlog r • F.A.world.W 2 (pairV F.action.J (pinned F)) (condense r φ)) atTop
      (𝓝 (∫ p,waveTest φ p ∂coneMeasure A)) := by
    apply (schwartz_limit ha h ht (waveTest φ)).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    rw [scaled_integral μ r hr (waveTest φ), h.absolute]; simp_rw [wave_scaling r hr]
end YM.TraceExtension
