import YM.Next.FLUCTUATIONS.Charts
import YM.SectorNext.VACUUM_NORMALIZATION.Depletion
import YM.Work.A15
import YM.Work.B04



/-!
# The narrow noise normalizer in calibrated Haar units

Not a statement identifying any *fine fluctuation* integral with its
Gaussian model. This Gaussian limit is for the scalar Z_beta of **one
noise bond** with the actual compact group price and Z chart, and the
remainder must still be charged per coarse bond. Also quantifies the
independent-plaquette obstruction. No simplicity or connectedness
assumption; handles zero-dimensional gauge too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open Filter Function Set Lattice RG Wilson Pressure Precision MeasureTheory
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
open Next.Fluctuations
variable {G : Gauge}

/-- A smaller closed log ball; explicit first-order chord normalization,
uniform through the ball. -/
theorem kernel_ball (A : ChartRatio G) (H : LocalRatio A) :
    ∃ r ε D : ℝ, 0 < r ∧ r < A.radius ∧ 0 < ε ∧ 0 < D ∧
    (∀ x : G.Color, ‖x‖ ≤ r → 0 ≤ A.J x ∧ A.J x ≤ 2 ∧
      ‖x‖/2 ≤ G.chord (G.lieExp x) ∧
      |G.chord (G.lieExp x)-‖x‖| ≤ D * ‖x‖^2) ∧
    ∀ y : G.El, y∉G.lieExp '' Metric.closedBall 0 r → ε ≤ G.price y := by
  let T : G.Color → G.Mat := fun a => G.mat (G.lieExp a)
  have ht : ∀ a : G.Color, HasDerivAt (fun v : ℝ => T (v • a)) (G.colorMat a) 0 := by
    intro a
    convert! ((by simpa only [zero_smul] using G.expDiff_zero : HasFDerivAt T G.colorMat.toContinuousLinearMap ((0:ℝ) • a)).comp_hasDerivAt (x:=(0:ℝ))) ((hasDerivAt_id' 0).smul_const a) using 1
    simp; rfl
  obtain ⟨C,r,hC,hr,he⟩ := chart_quadratic_cost T G.colorMat G.exp_jet.contDiffAt.analyticAt ht
  have hx (a : G.Color) (ha : ‖a‖ ≤ r) :
      |G.chord (G.lieExp a) - ‖a‖| ≤ (C/G.colorScale)*‖a‖^2 := by
    have hh := (he a).2 ha
    apply le_of_mul_le_mul_left _ G.colorScale_pos
    calc
      _ = |‖G.mat (G.lieExp a)-1‖-‖G.colorMat a‖| := by rw [G.colorMat_norm,← chord_dist,←mul_sub,abs_mul,abs_of_pos G.colorScale_pos]
      _ ≤ ‖G.mat (G.lieExp a)-1-G.colorMat a‖ := abs_norm_sub_norm_le ..
      _ = ‖T a - (T 0+G.colorMat a)‖ := by simp [T,sub_add_eq_sub_sub]
      _ ≤ C*‖a‖^2 := hh
      _ = _ := by have := G.colorScale_pos.ne'; field_simp
  obtain ⟨r',hr',hh⟩ := Metric.nhds_basis_closedBall.eventually_iff.1
    ((H.germ 0 (Metric.mem_ball_self H.patch)).continuousAt.eventually
      (gt_mem_nhds (show A.J 0 < 2 by rw [H.anchored]; norm_num)))
  let D := C/G.colorScale
  have hD : 0 < D := div_pos hC G.colorScale_pos
  let u := min (A.radius/2) (min (1/(2*D)) (min r' r))
  have hu : 0<u := lt_min (by have := H.patch; linarith) (lt_min (by positivity) (lt_min hr' hr))
  have hm : u < A.radius := lt_of_le_of_lt (min_le_left ..) (half_lt_self H.patch)
  have hb := show u ≤ min (1/(2*D)) (min r' r) from min_le_right ..
  have hU : u ≤ 1/(2*D) := hb.trans (min_le_left ..)
  have hp : u ≤ r := (hb.trans (min_le_right ..)).trans (min_le_right ..)
  obtain ⟨B,v,hB,hv,hb⟩ := log_chart_cost G
  let δ := min v (u/B)
  have hv : 0<δ := lt_min hv (div_pos hu hB)
  refine ⟨u,δ^2/2,D,hu,hm,by positivity,hD,fun x hh' => ?_,fun y hy => ?_⟩
  · have h0 : ‖x‖ ≤ r' := hh'.trans ((show u ≤ min (1/(2*D)) (min r' r) from min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..)))
    have hl := hx x (hh'.trans hp)
    refine ⟨(H.pos x (Metric.mem_ball.mpr (by rw [dist_zero_right]; exact hh'.trans_lt hm))).le,
      (show A.J x < 2 from hh (x:=x) (Metric.mem_closedBall.mpr (by rwa [dist_zero_right]))).le,?_,hl⟩
    have h : ‖x‖*(2*D) ≤ 1 := (le_div_iff₀ (by positivity)).mp (hh'.trans hU)
    have hy := (abs_le.mp hl).1
    change -(D*_) ≤ _ at hy
    nlinarith only [mul_le_mul_of_nonneg_right h (norm_nonneg x),hy]
  contrapose! hy
  have hi := G.chord_price y
  have ht : G.chord y ≤ δ := by nlinarith [G.chord_nonneg y]
  obtain ⟨hs,hw⟩ := hb y (ht.trans (min_le_left ..))
  refine ⟨_,Metric.mem_closedBall.mpr ?_,hs⟩
  rw [dist_zero_right]; apply hw.trans
  rw [mul_comm]; exact (le_div_iff₀ hB).mp (ht.trans (min_le_right ..))

-- Exact interior identity including restricting on both sides; doesn't
-- assume global chart parametrization.
lemma kernel_integral (A : ChartRatio G) (H : LocalRatio A) {r : ℝ} (hr : r<A.radius) (g : G.El→ℝ) (hg : Measurable g) :
    let B := Metric.closedBall (0:G.Color) r
    (∫ y in G.lieExp '' B, g y ∂G.probHaar) =
      ∫ x in B,(A.scale*A.J x)*g (G.lieExp x) := by
  intro B
  let M := Metric.ball (0:G.Color) A.radius
  let F := fun (x : G.Color) => ENNReal.ofReal (A.scale*A.J x)
  have hm := (show IsCompact (G.lieExp '' B) from (ProperSpace.isCompact_closedBall _ _).image G.lieExp_cont).measurableSet
  have hB := show MeasurableSet B from Metric.isClosed_closedBall.measurableSet
  have hM : MeasurableSet M := Metric.isOpen_ball.measurableSet
  have ht : B ⊆ M := Metric.closedBall_subset_ball hr
  have hv : G.lieExp '' B ⊆ G.lieExp '' M := image_mono ht
  have hF : Measurable F := (measurable_const.mul H.borel : Measurable (fun x : G.Color => A.scale * A.J x)).ennreal_ofReal
  have hk := integral_map (μ := (volume.restrict M).withDensity F) (φ:=G.lieExp) (f:= (G.lieExp '' B).indicator (g)) G.lieExp_cont.measurable.aemeasurable
    ((hg.indicator hm).aestronglyMeasurable)
  rw [H.actual,integral_indicator hm,Measure.restrict_restrict hm,inter_eq_self_of_subset_left hv,
    integral_withDensity_eq_integral_toReal_smul hF (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hk
  rw [hk]
  nth_rw 2 [← inter_eq_self_of_subset_left ht]; rw [← Measure.restrict_restrict hB,← integral_indicator hB]
  refine setIntegral_congr_fun hM fun x hx => ?_
  by_cases he : x∈B
  · rw [indicator_of_mem (mem_image_of_mem _ he),indicator_of_mem he]; unfold F; rw [ENNReal.toReal_ofReal (mul_nonneg H.scale.le (H.pos x hx).le),smul_eq_mul]
  have hh : G.lieExp x ∉ G.lieExp '' B := by
    rintro ⟨v,hv,he'⟩; exact he ((H.inject (ht hv) hx he') ▸ hv)
  rw [indicator_of_notMem he,indicator_of_notMem hh, smul_zero]


private abbrev dim (G : Gauge) := Module.finrank ℝ G.Color

/-- Only per noise bond! -/
def narrow (A : ChartRatio G) (κ : ℝ) := A.scale * (Real.pi / (κ/2)) ^ ((dim G:ℝ)/2)
lemma narrow_pos (A : ChartRatio G) (H : LocalRatio A) (κ : ℝ) (hk : 0<κ) : 0<narrow A κ := mul_pos H.scale (Real.rpow_pos_of_pos (by have := Real.pi_pos; positivity) _)

open Metric
private def bottle (A : ChartRatio G) (κ r t : ℝ) (x : G.Color) :=
  (closedBall 0 r).indicator (fun y => (A.scale*A.J y)*mouth G (κ*t^2) (G.lieExp y)) (t⁻¹ • x)

private theorem vanish_tail (A : ChartRatio G) (_ : LocalRatio A) {r ε κ : ℝ} (_ : 0<r) (_ : r<A.radius) (he : 0<ε) (hk : 0<κ)
    (hv : ∀ y : G.El,y∉G.lieExp '' closedBall 0 r → ε ≤ G.price y) :
    Tendsto (fun t : ℝ => t^dim G * (∫ y in (G.lieExp '' closedBall 0 r)ᶜ,mouth G (κ*t^2) y ∂G.probHaar)) atTop (𝓝 0) := by
  let B := (G.lieExp '' closedBall 0 r)ᶜ
  have he' : MeasurableSet B := ((ProperSpace.isCompact_closedBall _ _).image G.lieExp_cont).measurableSet.compl
  let a := κ*ε
  have ha : 0<a := mul_pos hk he
  have hh : Tendsto (fun t : ℝ => t ^ dim G * Real.exp (-t*a)) atTop (𝓝 0) := by
    have H := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (dim G)).comp (tendsto_id.atTop_mul_const ha)
    have ht : (fun t : ℝ => t^dim G*Real.exp (-t*a)) = fun t => (a^dim G)⁻¹ * (((id t)*a)^dim G*Real.exp (-(id t*a))) := by
      funext i; unfold id; rw [neg_mul,mul_pow]; field_simp; unfold a; ring
    rw [ht]
    simpa [Function.comp_def] using H.const_mul ((a^dim G)⁻¹)
  apply squeeze_zero' _ _ hh
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact mul_nonneg (pow_nonneg ht _) (setIntegral_nonneg he' fun y _ => (mouth_pos _ _ _).le)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
  have hy (y : G.El) (hyi : y∈B) : mouth G (κ*t^2) y ≤ Real.exp (-t*a) := by
    apply Real.exp_le_exp.mpr
    have hI := hv y hyi
    have hj : t*ε ≤ t^2*G.price y := mul_le_mul (by nlinarith) hI he.le (by positivity : 0≤t^2)
    unfold a
    nlinarith only [mul_le_mul_of_nonneg_left hj hk.le]
  apply le_trans (setIntegral_mono_on (μ:=G.probHaar) (mouth_int G _).integrableOn (integrableOn_const) he' hy)
  rw [setIntegral_const, smul_eq_mul]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (by simp [measureReal_le_one])

private lemma bottle_limit (A : ChartRatio G) (H : LocalRatio A) {κ r D : ℝ} (hk : 0<κ) (hr : 0<r)
    (he : ∀ x : G.Color, ‖x‖ ≤ r → 0 ≤ A.J x ∧ A.J x ≤ 2 ∧ ‖x‖/2 ≤ G.chord (G.lieExp x) ∧ |G.chord (G.lieExp x)-‖x‖| ≤ D * ‖x‖^2) :
    Tendsto (fun t : ℝ => ∫ x,bottle A κ r t x) atTop (𝓝 (narrow A κ)) := by
  let L := fun x : G.Color => A.scale * Real.exp (-(κ/2)*‖x‖^2)
  let b := κ/8
  let M := fun x : G.Color => 2*A.scale * Real.exp (-b*‖x‖^2)
  have hm : Integrable M := by
    have hg := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b:=(b:ℂ))
      (show 0<b from div_pos hk (by norm_num)) 0 (0:G.Color)).norm
    apply Integrable.const_mul _
    simpa [Complex.norm_exp,pow_two,Complex.mul_re] using hg
  have hh : (∫ x,L x)=narrow A κ := by
    unfold narrow L; rw [integral_const_mul,GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  rw [←hh]; refine tendsto_integral_filter_of_dominated_convergence M ?_ ?_ hm ?_
  · apply Eventually.of_forall; intro t
    have hv : Measurable (fun y : G.Color => (A.scale*A.J y)*mouth G (κ*t^2) (G.lieExp y)) := (measurable_const.mul H.borel).mul (((mouth_cont G _).comp G.lieExp_cont).measurable)
    exact (((hv.indicator isClosed_closedBall.measurableSet).comp (show Continuous (fun x : G.Color => t⁻¹ • x) from by fun_prop).measurable).aestronglyMeasurable)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    filter_upwards with x
    let y := t⁻¹ • x
    have Hn : t*‖y‖=‖x‖ := by unfold y; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le]; field_simp
    by_cases hy : y∈closedBall 0 r
    · obtain ⟨hJ,hJ',hj,hj'⟩ := he y (by simpa only [mem_closedBall,dist_zero_right] using hy)
      have hv : ‖x‖^2 ≤ 4*t^2*G.chord (G.lieExp y)^2 := by
        have hw : ‖x‖ ≤ 2*t*G.chord (G.lieExp y) := by linarith only [Hn,mul_le_mul_of_nonneg_left hj ht.le]
        nlinarith only [pow_le_pow_left₀ (norm_nonneg x) hw 2]
      have hh := G.chord_price (G.lieExp y)
      have hm : mouth G (κ*t^2) (G.lieExp y) ≤ Real.exp (-b*‖x‖^2) := Real.exp_le_exp.mpr (by
        rw [hh] at hv; unfold b; nlinarith only [mul_le_mul_of_nonneg_left hv hk.le])
      unfold bottle M
      rw [indicator_of_mem (show t⁻¹ • x∈_ from hy),Real.norm_of_nonneg (mul_nonneg (mul_nonneg H.scale.le hJ) (mouth_pos G (κ*t^2) (G.lieExp y)).le),mul_comm 2]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hJ' H.scale.le) hm (mouth_pos ..).le (by have := H.scale; positivity)
    unfold bottle M; rw [indicator_of_notMem (show t⁻¹ • x∉_ from hy),norm_zero]; have := H.scale; positivity
  refine Eventually.of_forall fun x => ?_
  let y := fun (t : ℝ) => t⁻¹ • x
  have hy : Tendsto y atTop (𝓝 0) := by simpa only [zero_smul] using
    ((tendsto_inv_atTop_zero (𝕜:=ℝ)).smul_const x)
  have ht (t : ℝ) (h : 0<t) : ‖y t‖ = t⁻¹*‖x‖ := by simp only [y,norm_smul,Real.norm_of_nonneg (inv_pos.mpr h).le]
  have hx := hy.eventually (closedBall_mem_nhds (0:G.Color) hr)
  have hg : Tendsto (fun t => t*G.chord (G.lieExp (y t))) atTop (𝓝 ‖x‖) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) (g:=fun t => t⁻¹ * (D * ‖x‖^2))
    · filter_upwards [hx,eventually_gt_atTop (0:ℝ)] with t hh h
      rw [Real.norm_eq_abs, show t*G.chord _-‖x‖= t*(G.chord (G.lieExp (y t))-‖y t‖) by rw [mul_sub,ht t h]; field_simp, abs_mul,abs_of_pos h]
      apply (mul_le_mul_of_nonneg_left (he (y t) (by simpa only [mem_closedBall,dist_zero_right] using hh)).2.2.2 h.le).trans
      rw [ht t h]; exact le_of_eq (by field_simp)
    simpa only [zero_mul] using (tendsto_inv_atTop_zero (𝕜:=ℝ)).mul_const (D * ‖x‖^2)
  have hh : Tendsto (fun t => Real.exp (-(κ/2)*(t*G.chord (G.lieExp (y t)))^2)) atTop (𝓝 (Real.exp (-(κ/2)*‖x‖^2))) := Real.continuous_exp.continuousAt.tendsto.comp ((hg.pow 2).const_mul _)
  have hJ : Tendsto (fun t => A.J (y t)) atTop (𝓝 1) := H.anchored ▸ ((H.germ 0 (mem_ball_self H.patch)).continuousAt.tendsto.comp hy)
  have H0 := ((hJ.const_mul A.scale).mul hh)
  simp only [mul_one] at H0
  refine H0.congr' ?_
  filter_upwards [hx] with t hV
  unfold bottle; rw [indicator_of_mem (show t⁻¹ • x ∈ closedBall 0 r from hV)]; congr 2
  unfold y; rw [mul_pow,G.chord_price]; ring_nf

/-- Positive inverse coupling convention, t large means width t⁻¹.
Scale and dim are the calibrated real ones. -/
theorem first_asymptotic (A : ChartRatio G) (H : LocalRatio A) (κ : ℝ) (hk : 0<κ) :
    Tendsto (fun t : ℝ => t ^ dim G * linkZ G (κ*t^2)) atTop (𝓝 (narrow A κ)) := by
  obtain ⟨r,ε,D,hr,hl,he,hD,hv,hu⟩ := kernel_ball A H
  have hh := (bottle_limit A H hk hr hv).add (vanish_tail A H hr hl he hk hu)
  simp only [add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  unfold bottle
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (f:= (closedBall _ _).indicator _) ht.le, smul_eq_mul,←mul_add]
  rw [integral_indicator isClosed_closedBall.measurableSet,← kernel_integral A H hl _ (mouth_cont G _).measurable,integral_add_compl (((ProperSpace.isCompact_closedBall _ r).image G.lieExp_cont).measurableSet) (mouth_int G _)]
  rfl








end YM.SectorNext.Vacuum
