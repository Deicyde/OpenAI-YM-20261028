import YM.TraceExtension.LogScaling

/-! Size consequences for the true PVM. Upper through energy, and nonzero
scaling in a compact strictly timelike window. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {G : Gauge} {C : Family G} {a : Extraction.Order} {S : Table C.book}
    {F : Spec.Final C a S} {μ : Measure E4} {A : ℝ}

def tally (μ : Measure E4) (r : ℝ) := μ {p | time p≤ r}
lemma scaled_tally (r : ℝ) (hr : 0<r) (μ : Measure E4) (t : ℝ) : tally (rescaled μ r) t= ENNReal.ofReal (Zlog r)*tally μ (t*r) := by
    unfold tally rescaled; rw [Measure.smul_apply, Measure.map_apply (by fun_prop) (isClosed_le Mink.clock_cont continuous_const).measurableSet]
    rw [show _ ⁻¹' _= _ from ?_]; rfl
    ext x; rw [Set.mem_preimage]; change time (r⁻¹ • x) ≤ t ↔ time x ≤ t*r; rw [Mink.clock_mul, mul_comm r⁻¹, ← div_eq_mul_inv, div_le_iff₀ hr]

def clock (i : ℕ) := (2:ℝ)^i
lemma clock_ge (i : ℕ) : 1≤ clock i := one_le_pow₀ (by norm_num)
lemma clock_high : Tendsto clock atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)

lemma log_high (h : TraceSpectrum F μ) (ha : 0 ≤ A) (ht : EuclideanAsymptotic F A) (B : ℝ) (hB : 1 ≤ B) :
    Tendsto (fun i => ENNReal.ofReal ((clock i)⁻¹^8)* tally μ (B*clock i)) atTop (𝓝 0) := by
    obtain ⟨C,hC,hv,hF⟩ := rescaled_energy ha h ht
    let L i := Real.log (clock i)
    have he : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp clock_high
    have hh := (tendsto_inv_atTop_zero.comp he).pow 2; rw [zero_pow (by decide : 2≠0)] at hh
    have hc : Tendsto (fun i=> ENNReal.ofReal ((L i)⁻¹^2)) atTop (𝓝 0) := by
       convert (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh) using 2 <;> simp
    let p:= ENNReal.ofReal (C*B^8); have hp:= ENNReal.Tendsto.const_mul (a:=p) hc (Or.inr ENNReal.ofReal_ne_top); rw [mul_zero] at hp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp (Eventually.of_forall (fun _=>zero_le)) ?_
    filter_upwards [clock_high.eventually hF,clock_high.eventually (eventually_gt_atTop 1)] with i hi ha
    have he : 0<L i := Real.log_pos ha
    have hg := hi B hB
    change tally (rescaled μ (clock i)) B≤p at hg; rw [scaled_tally _ (zero_lt_one.trans ha)] at hg
    rw [mul_comm p _]; apply le_trans ?_ (mul_le_mul_right hg _); apply le_of_eq; rw [← mul_assoc]; congr 1
    rw [← ENNReal.ofReal_mul (by positivity : 0≤ (L i)⁻¹^2)]; congr 1; unfold Zlog; unfold L at *; field_simp
lemma clock_slow : Tendsto (fun i=> ENNReal.ofReal (Zlog (clock i))* ENNReal.ofReal ((clock i)^7)) atTop (𝓝 0) := by
    let r : ℝ := (2:ℝ)⁻¹; have he := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (by norm_num [r] : |r|<1) |>.mul_const (Real.log 2 ^ 2)
    rw [zero_mul] at he; have hx := ENNReal.continuous_ofReal.continuousAt (x:=(0:ℝ))|>.tendsto; rw [ENNReal.ofReal_zero] at hx
    apply (hx.comp he).congr; intro i
    rw [← ENNReal.ofReal_mul (Zlog_nonneg ..)]; dsimp only [Function.comp_apply]; congr 1; unfold r Zlog clock; rw [Real.log_pow]; field_simp; rw [mul_assoc,← mul_pow]; norm_num

private lemma window (A : ℝ) (ha : 0<A) : ∃ f : E4→ℝ, HasCompactSupport f ∧ Continuous f ∧ tsupport f ⊆ {p| time p≤1} ∧ (∀ x, ‖f x‖ ≤ 1) ∧
    0 < ∫ x,f x ∂coneMeasure A := by
    let v := (1/2:ℝ) • basis timeAxis
    let K := inside ∩ {p:E4| time p<1}; have hk : IsOpen K := open_inside.inter (isOpen_lt Mink.clock_cont continuous_const); have hv : v∈K := by norm_num [v,K,inside]
    obtain ⟨r, hr, hx⟩ := Metric.mem_nhds_iff.mp (hk.mem_nhds hv)
    let B : ContDiffBump v := ⟨r/4,r/2,by positivity,by linarith⟩; have he : tsupport B ⊆ K := by rw [B.tsupport_eq]; apply subset_trans _ hx; apply Metric.closedBall_subset_ball; change r/2<r; linarith
    refine ⟨B,B.hasCompactSupport,B.continuous,fun p hp=>le_of_lt (show time p<1 from (he hp).2),fun x=>by rw [Real.norm_of_nonneg B.nonneg]; exact B.le_one,(integral_pos_iff_support_of_nonneg (fun _=> B.nonneg) (integrable_sensor (allows_cone A ha.le) _ B.continuous B.hasCompactSupport)).2 ?_⟩
    let D := Function.support B; have ht : D ⊆ K := (subset_tsupport B).trans he; have hf : D ⊆ cone := fun x hx=> (show ‖spatial x‖<time x from (ht hx).1).le
    have hm : MeasurableSet D := (isOpen_ne_fun B.continuous continuous_const).measurableSet
    change 0< (coneMeasure A) D; unfold coneMeasure; rw [withDensity_apply _ hm, restrict_restrict_of_subset hf]
    apply pos_iff_ne_zero.mpr; intro h
    have hh := (lintegral_eq_zero_iff (by fun_prop)).1 h
    have he : volume D ≠ 0 := by
        change volume (Function.support B) ≠ 0; rw [B.support_eq]; exact (measure_ball_pos _ _ B.rOut_pos).ne'
    haveI : NeBot (ae (volume.restrict D)) := ae_neBot.mpr (mt (Measure.restrict_eq_zero.mp) he)
    obtain ⟨p,hp,hg⟩ := (hh.and (ae_restrict_mem hm)).exists
    have he : 0< m p := ((Mink.strict_self _).1 (ht hg).1).2
    exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < A/(1536*Real.pi)* (m p)^2)).ne' hp

/-- Contradicts polynomial degree seven or lower along dyadic steps. -/
lemma does_not_fit (h : TraceSpectrum F μ) (ha : 0<A) (ht : EuclideanAsymptotic F A) (D : ℝ≥0) :
    ¬ ∀ᶠ i in atTop, tally μ (clock i) ≤ (D:ℝ≥0∞)*ENNReal.ofReal ((clock i)^7) := by
    obtain ⟨f,hk,hc,hs,hp,hA⟩ := window A ha
    intro hw
    let v i := rescaled μ (clock i)
    have hh := (laplace_compact _ _ ((eventually_gt_atTop 0).mono fun _ hx=> allows_rescaled h _ hx) (allows_cone A ha.le) (transform_limit h ha.le ht) f hc hk).comp clock_high
    have he : ∀ᶠ i in atTop, tally (v i) 1 ≤ (D:ℝ≥0∞)*(ENNReal.ofReal (Zlog (clock i))* ENNReal.ofReal ((clock i)^7)) := by
        filter_upwards [hw] with i hi; rw [show v i=rescaled _ _ from rfl,scaled_tally _ (zero_lt_one.trans_le (clock_ge i)),one_mul]; exact (mul_le_mul_right hi _).trans_eq (mul_left_comm ..)
    have hg := ENNReal.Tendsto.const_mul (a:=(D:ℝ≥0∞)) clock_slow (Or.inr ENNReal.coe_ne_top); rw [mul_zero] at hg
    have hv : Tendsto (fun i=> tally (v i) 1) atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg (Eventually.of_forall fun _=>zero_le) he
    have ht : Tendsto (fun i=> ∫ p,f p ∂v i) atTop (𝓝 0) := by
       apply tendsto_zero_iff_norm_tendsto_zero.mpr
       have hp : ∀ᶠ i in atTop, ‖∫ p,f p ∂v i‖≤ (tally (v i) 1).toReal := by
           filter_upwards [he] with i hi; let W := {p:E4| time p≤1}
           rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=W) (fun x hx => image_eq_zero_of_notMem_tsupport (fun e=> hx (hs e)))]
           apply (norm_setIntegral_le_of_norm_le_const (lt_of_le_of_lt hi (by finiteness)) (fun x _=> hp x)).trans_eq; rw [one_mul]; rfl
       exact squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) hp (by simpa using! ((ENNReal.tendsto_toReal (a:=0) (by simp)).comp hv))
    exact hA.ne' (tendsto_nhds_unique hh ht)
end YM.TraceExtension
