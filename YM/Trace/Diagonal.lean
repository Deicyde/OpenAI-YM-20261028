import YM.Trace.Weight
import YM.Fields.System

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.Trace
open Boundary Function Filter MeasureTheory Set Complex Spectral
open scoped Topology BigOperators ENNReal NNReal InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

variable {H : Hilbert} (T : Orbit H V) (P : PVM H V)
    (ht : T.Spectrum P) (v : Probe V →L[ℂ] H)
    (hc : ∀ p : V, ∀ f : Probe V, v (Probe.ahead p f) = T.translation p (v f))

abbrev price (f : Probe V) (p : V) := (‖plus f p‖ₑ)^2

def charge (μ : Measure V) (f : Probe V) := μ.withDensity (price f)

lemma measurable_price (f : Probe V) : Measurable (price f) := by unfold price; fun_prop
lemma value_price (f : Probe V) (p : V) : (price f p).toReal = ‖plus f p‖^2 := by
  simp only [price,ENNReal.toReal_pow,toReal_enorm]
lemma price_ofReal (f : Probe V) (p : V) : (price f p) = ENNReal.ofReal (‖plus f p‖^2) := by
  rw [price,← _root_.ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

instance charge_finite (μ : Measure V) [IsFiniteMeasure μ] (f : Probe V) : IsFiniteMeasure (charge μ f) := by
  refine ⟨?_⟩
  rw [charge,withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ,price_ofReal]
  let B := Probe.size 0 0 (plus f)
  refine (lintegral_mono (g:=fun _=> ENNReal.ofReal (B^2)) ?_).trans_lt ?_
  · intro x; dsimp only; exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
      (SchwartzMap.norm_le_seminorm ℂ (plus f) _) 2)
  simp only [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ..)

lemma char_charge (μ : Measure V) [IsFiniteMeasure μ] (f : Probe V) (p : V) :
    charFun (charge μ f) p = ∫ x, star (plus f x) * plus f x * Probe.plane x p ∂μ := by
  rw [charFun_apply, charge, integral_withDensity_eq_integral_toReal_smul (measurable_price ..)
    (Filter.Eventually.of_forall (fun p => by finiteness))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change _ • cexp _ = _
  rw [value_price,Complex.real_smul,ofReal_pow]
  congr 1
  rw [mul_comm]; rw [Complex.star_def, Complex.mul_conj,Complex.normSq_eq_norm_sq]; norm_cast

lemma inner_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → H}
    (hf : Integrable f μ) (b : H) : inner ℂ (∫ x,f x ∂μ) b = ∫ x, inner ℂ (f x) b∂μ := by
  rw [show inner ℂ _ b=(starRingEnd ℂ) (inner ℂ b _) from (inner_conj_symm ..).symm,
    ← _root_.integral_inner hf b, ← integral_conj]
  simp_rw [inner_conj_symm]

include hc
lemma smear_orbit (a b : Probe V) (ha : CC a) :
    v (conv a b) = ∫ x, a x • T.translation x (v b) := by rw [wave_integral_test v a b ha]; simp_rw [hc]

include ht
set_option maxHeartbeats 1000000
lemma phase_conv (a b : Probe V) (ha : CC a) (y : V) :
    charFun (P.diagonal (v (conv a b))) y =
     ∫ (p : V), ∫ (r : V), star (a p) * a r * (∫ u, Probe.plane u (y+r-p) ∂P.diagonal (v b)) := by
  let B := v b
  let f (p : V) := a p • T.translation p B
  rw [ht (v (conv a b)) y,smear_orbit T v hc _ _ ha]
  have hf : Integrable f := by
    exact (a.continuous.smul (T.moves B)).integrable_of_hasCompactSupport ha.smul_right
  rw [← (T.translation _).integral_comp_comm hf,inner_integral hf]
  apply integral_congr_ae; filter_upwards with p
  rw [← integral_inner ((T.translation y).integrable_comp hf)]
  apply integral_congr_ae; filter_upwards with r
  have same (x : H) : inner ℂ (T.translation p B) (T.translation p x) = inner ℂ B x := by
     let L : H→ₗᵢ[ℂ] H := ⟨(T.translation p).toLinearMap,T.unitary p⟩
     exact L.inner_map_map ..
  have hp := same (T.translation (y+r-p) B)
  rw [← ContinuousLinearMap.comp_apply (g:=T.translation p) (f:=T.translation (y+r-p)), T.sends, show p+(y+r-p)=y+r by abel] at hp
  change inner ℂ (a p • T.translation p B) (T.translation y (a r • T.translation r B)) = _
  rw [map_smul, inner_smul_left, inner_smul_right,← ContinuousLinearMap.comp_apply (g:=T.translation y) (f:=T.translation r),T.sends,hp,← ht B]
  rw [charFun_apply,starRingEnd_apply,← mul_assoc]; rfl

set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 2000000
theorem charge_convolution (a b : Probe V) (ha : CC a) :
    charge (P.diagonal (v b)) a = P.diagonal (v (conv a b)) := by
  apply Measure.ext_of_charFun
  ext1 y
  let ν := P.diagonal (v b)
  change charFun (charge ν a) y = _
  rw [char_charge, phase_conv T P ht v hc a b ha]
  let L (u p r : V) := star (a p) * a r * Probe.plane u (y+r-p)
  have hi : Integrable (fun z : (V × V) × V => L z.1.2 z.1.1 z.2) (((volume : Measure V).prod ν).prod volume) := by
    have hu : Integrable (fun z : V×V => ‖a z.1‖) (volume.prod ν) := (a.integrable.norm.comp_fst (ν:=ν))
    apply (hu.mul_prod a.integrable.norm).mono'
    · unfold L
      fun_prop (disch := exact a.continuous)
    filter_upwards with k
    exact le_of_eq (by simp [L])
  have hK (p : V) : Integrable (fun k : V × V => L k.1 p k.2) (ν.prod volume) := by
    apply (a.integrable.norm.comp_snd ν).const_mul ‖a p‖ |>.mono'
    · unfold L; fun_prop (disch := exact a.continuous)
    filter_upwards with k; simp [L]
  have hfub (u : V) : star (plus a u) * plus a u * Probe.plane u y = ∫ p, ∫ r,L u p r := by
    have he p r : L u p r = ((starRingEnd ℂ) (Probe.plane p u * a p) * (Probe.plane r u * a r)) * Probe.plane u y := by
      have hs := Probe.plane_inverse u p
      dsimp only [L]; rw [sub_eq_add_neg, Probe.plane_add,Probe.plane_add,hs,Probe.plane_dot u r,Probe.plane_dot u p,map_mul]
      rw [Complex.star_def]; ring
    simp_rw [he,plus_eq, Complex.star_def]
    rw [← _root_.integral_conj]
    rw [← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_mul_const]
    apply integral_congr_ae
    filter_upwards with p
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
  calc
    _ = ∫ u, (∫ p, ∫ r, L u p r) ∂ν := by
      refine integral_congr_ae (.of_forall fun u => by dsimp only; exact hfub u)
    _ = _ := ?_
  rw [(show Integrable (uncurry fun u p => ∫ r, L u p r) (ν.prod volume) from hi.integral_prod_left.swap) |> integral_integral_swap]
  apply integral_congr_ae
  filter_upwards with p
  rw [(show Integrable (uncurry (fun u => L u p)) (ν.prod volume) from hK p) |> integral_integral_swap]
  apply integral_congr_ae
  filter_upwards with r
  dsimp only [L]
  rw [MeasureTheory.integral_const_mul]
lemma charge_symm (a b : Probe V) (ha : CC a) (hb : CC b) :
    charge (P.diagonal (v b)) a = charge (P.diagonal (v a)) b := by
  simp_rw [charge_convolution T P ht v hc a b ha, ← conv_comm b a, charge_convolution T P ht v hc b a hb]

set_option maxHeartbeats 1500000
/-- Resolve the incompatible local convolutions over a countable patch cover, not by assuming
an unsmeared vector in the Hilbert space. -/
theorem common_diagonal : ∃ μ : Measure V, ∀ f : Probe V, CC f →
    charge μ f = P.diagonal (v f) := by
  obtain ⟨z,hz,hP⟩ := plus_fits (V:=V)
  let W (i) : Set V := Function.support (plus (z i)); let D := disjointed W
  let w (i) := price (z i); let A (i) := ((P.diagonal (v (z i))).restrict (D i)).withDensity (w i)⁻¹
  have hWm (i): MeasurableSet (W i) := (plus (z i)).continuous.isOpen_support.measurableSet
  have hDm (i) : MeasurableSet (D i) := MeasurableSet.disjointed hWm _
  have hd : univ = ⋃ i, D i := Eq.symm (Subset.antisymm (subset_univ _) (fun x _ => (iUnion_disjointed (f:=W)) ▸
     mem_iUnion.mpr (hP x)))
  refine ⟨Measure.sum A, fun f hf => ?_⟩
  have he (i) : charge (A i) f = (P.diagonal (v f)).restrict (D i) := by
    have hw := measurable_price (z i)
    have hm := (z i).continuous.measurable
    change (((P.diagonal (v (z i))).restrict (D i)).withDensity (w i)⁻¹).withDensity (price f) = _
    rw [← withDensity_mul _ ((measurable_price _).inv) (measurable_price _),mul_comm,
      withDensity_mul .., ← restrict_withDensity (hDm i) _]
    rw [← charge.eq_def, charge_symm T P ht v hc f _ hf (hz i),charge,restrict_withDensity (hDm i),
      ← withDensity_mul _ hw hw.inv]
    convert_to ((P.diagonal (v f)).restrict (D i)).withDensity 1= _ using 1
    · apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem (hDm i)] with p hp
      simp only [Pi.mul_apply,Pi.inv_apply, Pi.one_apply]
      refine ENNReal.mul_inv_cancel (pow_ne_zero _ ?_) (by finiteness)
      simpa only [ne_eq,enorm_eq_zero] using! (disjointed_subset W i hp)
    · exact withDensity_one
    exacts [measurable_price _,hw.inv]
  rw [charge, withDensity_sum]; change Measure.sum (fun i => charge (A i) f) = _
  simp_rw [he]; rw [← Measure.restrict_iUnion (disjoint_disjointed W) hDm, ← hd, Measure.restrict_univ]

omit ht hc
section
variable {μ : Measure V} (hμ : ∀ f : Probe V, CC f → charge μ f = P.diagonal (v f))
include hμ

lemma total_CC (f : Probe V) (hf : CC f) : (∫⁻ x, price f x ∂μ) = ENNReal.ofReal (‖v f‖^2) := by
  have hx : Integrable (fun x : V => (1:ℝ)) (P.diagonal (v f)) := integrable_const _
  rw [← hμ f hf] at hx
  have hi : Integrable (fun x => ‖plus f x‖^2) μ := Integrable.congr
    ((integrable_withDensity_iff (measurable_price f) (.of_forall fun x => by finiteness)).mp hx)
    (.of_forall fun x => one_mul _ |>.trans (value_price f x))
  have H := integral_withDensity_eq_integral_toReal_smul (μ:=μ) (measurable_price f)
    (Filter.Eventually.of_forall fun _ => by finiteness) (fun _ => (1:ℝ))
  simp only [smul_eq_mul, mul_one, ← charge.eq_def,hμ f hf,MeasureTheory.integral_const,value_price,
    MeasureTheory.integral_const, P.same MeasurableSet.univ, P.all] at H
  rw [show (∫⁻ x, price f x ∂μ)=_ from (by simp_rw [price_ofReal f]; rfl),
      ← ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun x => sq_nonneg _)]
  rw [← H]; simp

lemma diagonal_growth : ∃ A : ℝ≥0∞, ∃ n, Growth μ A n ∧ A < ∞ := by
  have hp := (plus (initial V)).continuous.continuousAt (x:=0)
  obtain ⟨δ,hδ,he⟩ := Metric.continuousAt_iff.mp hp ((1:ℝ)/2) (by norm_num)
  let c := min 1 (δ/2); have hc' : 0<c := lt_min one_pos (half_pos hδ)
  obtain ⟨n,L,hL,hN⟩ := normalized_cost v (initial V)
  refine ⟨ENNReal.ofReal (4*L^2/(c^2)^n),2*n,fun R hr => ?_,by finiteness⟩
  let t := R/c; have ht' : 1 ≤ t := (one_le_div hc').2 ((min_le_left ..).trans hr)
  let f := normalized (initial V) t
  have hff (x : V) (h : x ∈ Metric.closedBall 0 R) : (1/2:ℝ) ≤ ‖plus f x‖ := by
    have hx : ‖x‖ ≤ R := by simpa using Metric.mem_closedBall.mp h
    have hh := he (show dist (t⁻¹ • x) 0 < δ by
       rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (by positivity)]
       have hm : 0<R := zero_lt_one.trans_le hr
       calc t⁻¹ * ‖x‖ ≤ t⁻¹ * R := mul_le_mul_of_nonneg_left hx (by positivity)
            _ = c := by dsimp [t]; field_simp
            _ < δ := (min_le_right _ _).trans_lt (by linarith))
    rw [plus_initial] at hh
    change 1/2 ≤ ‖plus (normalized (initial V) t) x‖
    rw [plus_normalized _ (lt_of_lt_of_le zero_lt_one ht')]
    have hy := abs_le.mp (show |1-‖plus (initial V) (t⁻¹ • x)‖| ≤ dist (plus (initial V) (t⁻¹ • x)) 1 by
       simpa only [dist_eq_norm,Real.norm_eq_abs,norm_one,abs_sub_comm,norm_sub_rev] using
        dist_norm_norm_le (plus (initial V) (t⁻¹ • x)) (1:ℂ))
    linarith
  calc
    μ _ ≤ μ {x|(4:ℝ≥0∞)⁻¹ ≤ price f x} := measure_mono (fun x hx => by
         change (4:ℝ≥0∞)⁻¹≤price f x; rw [price_ofReal,show (4:ℝ≥0∞)⁻¹=ENNReal.ofReal ((1/2)^2) by rw [show (1/2)^2=(1:ℝ)/4 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num]
         exact ENNReal.ofReal_le_ofReal (by nlinarith [hff x hx]))
    _ ≤ (∫⁻ x,price f x ∂μ) / (4:ℝ≥0∞)⁻¹ := meas_ge_le_lintegral_div (measurable_price ..).aemeasurable (by simp) (by simp)
    _ = ENNReal.ofReal (4 * ‖v f‖^2) := by
       rw [total_CC P v hμ f (normalized_CC initial_CC t), ENNReal.ofReal_mul (by norm_num), div_eq_mul_inv,inv_inv]
       rw [mul_comm]; norm_num
    _ ≤ ENNReal.ofReal (4 * (L*t^n)^2) := ENNReal.ofReal_le_ofReal (by gcongr; exact hN t ht')
    _ = _ := by
       rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by positivity)]
       unfold t; congr 1; ring
-- shift_norm of inequality helper
end
lemma total_schwartz {μ : Measure V} (h : ∀ f : Probe V, CC f → charge μ f=P.diagonal (v f))
    (u : Probe V) : (∫ x, ‖plus u x‖^2∂μ) = ‖v u‖^2 := by
  obtain ⟨A,n,hg,hA⟩ := diagonal_growth P v h
  let f := cutTest u
  have hf : Tendsto f atTop (𝓝 u) := cutTest_limit u
  have hp : Tendsto (fun r : ℝ => ∫ x, ‖plus (f r) x‖^2∂μ) atTop (𝓝 (∫ x, ‖plus u x‖^2∂μ)) := by
    let g (r) := plus (f r); let w := plus u; have h' : Tendsto g atTop (𝓝 w) := plus.continuous.continuousAt.tendsto.comp hf
    obtain ⟨C,hC, hc⟩ : ∃ C : ℝ,0≤ C ∧ ∀ᶠ r : ℝ in atTop, orderCost (g r) (n+1) ≤ C := ⟨orderCost w (n+1) + 1,
      by linarith [orderCost_nonneg w (n+1)], (((continuous_orderCost _).continuousAt.tendsto.comp h').eventually
        (gt_mem_nhds (lt_add_one (orderCost w (n+1))))).mono (fun _ e => e.le)⟩
    refine tendsto_integral_filter_of_dominated_convergence (fun x => (C * 2^(n+1))^2 * (weight (n+1) x)⁻¹) (.of_forall fun i=>
      ?_) ?_ ((hg.integrable_weight μ hA).const_mul _) (.of_forall fun i => ?_)
    · exact ((g _).continuous.norm.pow _).aestronglyMeasurable
    · filter_upwards [hc] with r hr
      let G := g r
      filter_upwards with x
      have hw := weighted_test G (n+1) x; rw [Real.norm_of_nonneg (sq_nonneg _)]
      have H := inv_nonneg.mpr (weight_pos (n+1) x).le
      have hG := orderCost_nonneg G (n+1)
      let k := weight (n+1) x
      calc ‖G x‖^2 ≤ _ := pow_le_pow_left₀ (norm_nonneg _) hw _
           _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (mul_nonneg hG (by positivity)) H) (show orderCost G (n+1) * 2^(n+1) * k⁻¹ ≤ C * 2^(n+1) * k⁻¹ from mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity)) H) _
           _ ≤ (C*2^(n+1)) ^ 2 * _ := ?_
      rw [mul_pow]; gcongr; rw [pow_two]; apply mul_le_of_le_one_left (by have := weight_pos (n+1) x; positivity)
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg x]))
    · have he := ((by fun_prop : Continuous fun v : Spark.Air 0 V => v 0) |>.continuousAt.tendsto.comp ((Spark.jet i 0).continuous.continuousAt.tendsto.comp h'))
      simpa only [Function.comp_apply,Spark.Jet, iteratedFDeriv_zero_apply] using he.norm.pow 2
  apply tendsto_nhds_unique_of_eventuallyEq hp ((v.continuous.continuousAt.tendsto.comp hf).norm.pow _)
  filter_upwards with r
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ => sq_nonneg _) (by exact ((plus _).continuous.norm.pow _).aestronglyMeasurable)]
  simp_rw [← price_ofReal]; rw [total_CC P v h (f r) (cutTest_CC _ r), ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl


lemma spectral_inner {μ : Measure V} (h : ∀ f : Probe V, CC f → charge μ f=P.diagonal (v f))
    (f g : Probe V) :
    inner ℂ (v f) (v g) = ∫ p, inner ℂ (plus f p) (plus g p) ∂μ := by
  obtain ⟨A,n,hg,hA⟩ := diagonal_growth P v h
  let q (f g : Probe V) (x : V) := inner ℂ (plus f x) (plus g x)
  have hi f g : Integrable (q f g) μ := by
    refine hg.integrable_prod hA (plus f) (plus g) _ ((by unfold q; exact (Continuous.inner (𝕜:=ℂ) (plus f|>.continuous)
      (plus g|>.continuous)) : Continuous _).aestronglyMeasurable) 1 ?_
    simpa only [one_mul] using fun x => norm_inner_le_norm (𝕜:=ℂ) (plus f x) (plus g x)
  have hd f : Integrable (fun p => ‖plus f p‖^2) μ := by
    refine hg.integrable_prod hA (plus f) (plus f) _ ((plus f).continuous.norm.pow 2).aestronglyMeasurable 1 ?_
    intro x; rw [norm_pow, Real.norm_of_nonneg (norm_nonneg _), sq, one_mul]
  have he (b : Probe V) : (inner ℂ (v f) (v b)).re = (∫ p, q f b p ∂μ).re := by
    have hm : ∀ x, ‖plus (f+b) x‖^2 = ‖plus f x‖^2 + 2* (q f b x).re+‖plus b x‖^2 := by
      intro x; rw [map_add,add_apply]; exact @norm_add_sq ℂ ℂ _ _ _ _ _
    have ht := total_schwartz P v h (f+b)
    rw [v.map_add, @norm_add_sq ℂ H _ _ _] at ht
    have hd' : Integrable (fun x => 2 * (q f b x).re) μ := ((hi f b).re).const_mul _
    simp_rw [hm] at ht
    rw [integral_add (by apply (hd f).add hd') (hd b), integral_add (hd f) hd', MeasureTheory.integral_const_mul,
      show (∫ p, (q f b p).re ∂μ)=_ from _root_.integral_re (hi f b), total_schwartz P v h,
      total_schwartz P v h] at ht
    change (inner ℂ _ _).re = _; rw [← RCLike.re_to_complex]
    exact (mul_right_inj' (by norm_num : (2:ℝ)≠0)).mp (add_left_cancel (add_right_cancel ht) |>.symm)
  refine Complex.ext (he g) ?_
  have hI := he (I • g)
  have hh : q f (I • g) = I • q f g := by
    ext1 p; change inner ℂ _ (plus (I • g) p) = I • _
    rw [map_smul,smul_apply,inner_smul_right]; rfl
  rw [map_smul,inner_smul_right,hh, show (∫ p, (I • q f g) p ∂μ)=_ from MeasureTheory.integral_smul (μ:=μ) I (q f g)] at hI
  simpa only [smul_eq_mul,mul_re,I_re, I_im,one_mul,zero_mul,zero_sub, neg_inj] using! hI
include ht hc
/-- No prior assumption that a point field acts on the vacuum. -/
theorem orbit_measure {K : Set V} (hK : P.region Kᶜ=0) (hm : MeasurableSet K) :
     ∃ μ : Measure V, Tempered μ ∧ μ Kᶜ=0 ∧ ∀ f g : Probe V,
        inner ℂ (v f) (v g) = ∫ p, star (plus f p) * plus g p ∂μ := by
  obtain ⟨μ,hμ⟩ := common_diagonal T P ht v hc
  obtain ⟨A,n,hg,hA⟩ := diagonal_growth P v hμ
  refine ⟨μ,⟨n,A.toReal,(by rwa [ENNReal.ofReal_toReal hA.ne])⟩,?_,fun f g => ?_⟩
  swap; · simpa only [RCLike.inner_apply,Complex.star_def,mul_comm] using spectral_inner P v hμ f g
  have hz (f : Probe V) (hf : CC f) : (charge μ f) Kᶜ=0 := by
     rw [hμ f hf]; refine (P.null_pair hm.compl _).2 ?_; simp [hK]
  obtain ⟨r,hr,hS⟩ := plus_fits (V:=V)
  suffices ∀ᵐ x ∂μ, x∈K by rwa [ae_iff] at this
  have hi (i) : ∀ᵐ x ∂μ, price (r i) x ≠ 0 → x ∈ K := by
     rw [ae_iff]
     rw [show {a | ¬ (price (r i) a ≠ 0 → a ∈ K)}={a|price (r i) a ≠ 0} ∩ Kᶜ from Set.ext (fun _=> by simp)]
     exact withDensity_apply_eq_zero (measurable_price _) |>.mp (hz _ (hr i))
  filter_upwards [ae_all_iff.mpr hi] with x hx
  obtain ⟨i,he⟩ := hS x
  exact hx i (pow_ne_zero _ (by simpa using! he))
end YM.Trace
