import YM.LocalH.Chart
/-!
# Actual volume

Glue (inversion-free overlap law) by compact averaging, not assuming
uniqueness of any local group volume. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalH
open Function Filter MeasureTheory Set Metric Precision NormedSpace
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ENNReal

variable (G : Gauge)
private def bud (s : Set G.Color) := Measure.map G.lieExp ((volume.restrict s).withDensity (fun x : G.Color => ENNReal.ofReal (spin G x)))
private lemma bud_e (s : Set G.Color) {A : Set G.El} (h : MeasurableSet A) :
    bud G s A=∫⁻ x in G.lieExp ⁻¹' A ∩ s, ENNReal.ofReal (spin G x) := by
  unfold bud
  have he := G.lieExp_cont.measurable
  rw [Measure.map_apply he h,withDensity_apply _ (he h), Measure.restrict_restrict (he h)]

private lemma bud_hit (U : Set G.El) (s : Set G.Color) (h : Geom G U s) (hu : (1:G.El)∈U)
    (hp : ∀ i∈s, 0 ≤ spin G i) {A : Set G.El} (hA : MeasurableSet A) (ht : A⊆U) (u : G.El) :
    bud G s ((fun x => u*x) ⁻¹' A) = bud G s (A∩ imageHit G U u) := by
  let T := imageHit G U u
  let V := (fun x : G.El => u*x) ⁻¹' A
  have he := G.lieExp_cont.measurable
  have hV : MeasurableSet V := measurable_id.const_mul u hA
  have hT : MeasurableSet T := (measurable_id.const_mul u⁻¹) h.1.measurableSet
  rw [bud_e G _ hV, bud_e G _ (hA.inter hT)]
  let W := G.lieExp ⁻¹' V ∩ s
  have hw : MeasurableSet W := (he hV).inter h.2.1.measurableSet
  let F := move G u
  have ha (x : G.Color) (hx : x∈W) : G.lieExp (F x)=u*G.lieExp x := h.2.2.2.1 (ht hx.1)
  have hc (x : G.Color) (hx : x∈W) : F x∈ s := h.2.2.2.2.1 (ht hx.1)
  have hi : InjOn F W := by
    intro i hi j hj hh
    have hv := (ha i hi).symm.trans ((congr_arg _ hh).trans (ha j hj)); exact h.2.2.1.injOn hi.2 hj.2 (mul_left_cancel hv)
  have hg : G.lieExp ⁻¹' (A∩ T) ∩ s=F '' W := by
    ext x; constructor
    · rintro ⟨⟨H1,H2⟩,H3⟩
      let y := move G u⁻¹ x
      have hh : G.lieExp y=u⁻¹*G.lieExp x := h.2.2.2.1 H2
      have hw : y∈s:=h.2.2.2.2.1 H2
      refine ⟨y, ⟨?_,hw⟩,?_⟩
      · change u*G.lieExp y∈A; rw [hh,mul_inv_cancel_left]; exact H1
      unfold F move; rw [hh, mul_inv_cancel_left]; exact h.2.2.1 H3
    rintro ⟨i,h1,rfl⟩
    refine ⟨⟨?_,?_⟩,hc _ h1⟩
    · rw [ha i h1]; exact h1.1
    · change u⁻¹*G.lieExp (F i)∈U; rw [ha _ h1, inv_mul_cancel_left]
      exact h.2.2.2.2.2.1 h1.2
  change (∫⁻ _ in W,_) = ∫⁻ _ in G.lieExp ⁻¹' (A ∩ T) ∩ s,_
  rw [hg,lintegral_image_eq_lintegral_abs_det_fderiv_mul _ hw (fun x hx => (move_drifts G h (ht hx.1)).hasFDerivWithinAt) hi]
  apply setLIntegral_congr_fun hw; intro x hx
  dsimp only
  change ENNReal.ofReal _ = ENNReal.ofReal |(fderiv ℝ F x).det| *ENNReal.ofReal (spin G (F x))
  rw [← ENNReal.ofReal_mul (abs_nonneg _),mul_comm,← abs_of_nonneg (hp _ (hc _ hx)),← abs_mul,show spin G (F x)*_ = spin G x from spins G h hu x (ht hx.1), abs_of_nonneg (hp _ hx.2)]

section averaging
variable (μ : Measure G.El) [IsFiniteMeasure μ]
private lemma roll (U A : Set G.El) (H : MeasurableSet U) (h : MeasurableSet A)
    (S : ∀ u : G.El, μ ((fun x => u*x) ⁻¹' A) = μ (A∩ imageHit G U u)) : μ univ*G.probHaar A=G.probHaar U * μ A := by
  classical
  let p (u x : G.El) : ℝ≥0∞ := if u*x∈A then 1 else 0
  let q (u x : G.El) : ℝ≥0∞ := if x∈A ∧ u⁻¹*x∈U then 1 else 0
  have he (u) : (∫⁻ x,p u x ∂μ) = ∫⁻ x,q u x ∂μ := by
    let V := (fun x : G.El => u*x) ⁻¹' A
    let W := A∩ imageHit G U u
    have hw : p u=V.indicator 1 := by ext x; simp only [V,p,indicator,mem_preimage,Pi.one_apply]
    have hw' : q u=W.indicator 1 := by ext x; simp only [W,q,indicator, mem_inter_iff,imageHit,mem_setOf_eq,Pi.one_apply]
    rw [hw,hw',lintegral_indicator_one (show MeasurableSet V from measurable_id.const_mul u h),lintegral_indicator_one (show MeasurableSet W from h.inter (measurable_id.const_mul u⁻¹ H))]
    exact S u
  have ht (x : G.El) : (∫⁻ u,p u x∂G.probHaar)=G.probHaar A := by
    let V := (fun u => u*x) ⁻¹' A
    have hh : (fun u => p u x)=V.indicator 1 := by ext x; simp only [V,p,indicator,mem_preimage,Pi.one_apply]
    rw [hh,lintegral_indicator_one (show MeasurableSet V from (measurable_id.mul_const x) h)]
    exact (measurePreserving_mul_right G.probHaar x).measure_preimage h.nullMeasurableSet
  have ht' (x : G.El) : (∫⁻ u,q u x∂G.probHaar) = A.indicator (fun _ => G.probHaar U) x := by
    by_cases hh : x∈A
    · rw [indicator_of_mem hh]
      let V := (fun u => u⁻¹*x) ⁻¹' U
      have hx : (fun u => q u x)=V.indicator 1 := by ext u; simp only [V,q,indicator,mem_preimage,hh,true_and, Pi.one_apply]
      rw [hx,lintegral_indicator_one ((measurable_inv.mul_const x) H)]
      exact ((measurePreserving_mul_right G.probHaar x).comp G.preserve_inv).measure_preimage H.nullMeasurableSet
    simp only [q,hh,false_and, ↓reduceIte,indicator_of_notMem hh]; simp
  have hp : Measurable (uncurry p) := Measurable.ite ((measurable_fst.mul measurable_snd) h) measurable_const measurable_const
  have hq : Measurable (uncurry q) := Measurable.ite ((measurable_snd h).inter ((measurable_fst.inv.mul measurable_snd) H)) measurable_const measurable_const
  calc
    _ = ∫⁻ x: G.El, ∫⁻ u,p u x∂G.probHaar ∂μ := by simp_rw [ht,lintegral_const,mul_comm]
    _ = ∫⁻ u, ∫⁻ x,p u x ∂μ ∂G.probHaar := (lintegral_lintegral_swap hp.aemeasurable).symm
    _ = ∫⁻ x,∫⁻ u,q u x∂G.probHaar ∂μ := by simp_rw [he]; exact lintegral_lintegral_swap hq.aemeasurable
    _ = _ := by simp_rw [ht']; rw [lintegral_indicator h]; simp
end averaging

/-- Production. `Pos` quantified inside open ball; shrink freely before use. -/
lemma actual : ∃ X : ChartRatio G, LocalRatio X := by
  have he := spin_zero G
  have hp : Continuous (spin G) := continuous_iff_continuousAt.mpr fun x => (spin_deriv G x).continuousAt
  have hr := hp.continuousAt.preimage_mem_nhds (x:=0) (Ioo_mem_nhds (show (1/2:ℝ)<spin G 0 by rw [he]; norm_num) (show spin G 0<2 by rw [he]; norm_num))
  obtain ⟨R,hR,H⟩ := Metric.mem_nhds_iff.mp hr
  obtain ⟨r,hr',h⟩ := geom_patch G
  let a := min r R
  let s := ball (0:G.Color) a
  let U := G.lieExp '' s
  let μ := bud G s
  have hg := h a (min_le_left ..)
  have hy : 0<a := lt_min hr' hR
  have ha : (0:G.Color)∈s := mem_ball_self hy
  have HV : MeasurableSet s:=hg.2.1.measurableSet
  have HU : MeasurableSet U:=hg.1.measurableSet
  have hu : (1:G.El)∈U:=⟨0,ha,G.mat_lieExp_zero⟩
  have hb (x : G.Color) (hx : x∈s) : 1/2<spin G x ∧ spin G x<2 := H (ball_subset_ball (min_le_right ..) hx)
  have hi (x : G.Color) (hx : x∈s) : 0 < spin G x := lt_trans (by norm_num) (hb _ hx).1
  have hx : μ univ=∫⁻ x in s, ENNReal.ofReal (spin G x) := by unfold μ; rw [bud_e G s MeasurableSet.univ,preimage_univ,univ_inter]
  have hm : μ univ ≠ 0 := by
    rw [hx]; apply ne_of_gt
    have hy : 0 < ∫⁻ x in s, ENNReal.ofReal (1/2) := by simp only [lintegral_const,Measure.restrict_apply_univ]; exact ENNReal.mul_pos (by norm_num) ((hg.2.1.measure_pos volume ⟨0,ha⟩).ne')
    exact hy.trans_le (setLIntegral_mono' HV fun i hh ↦ ENNReal.ofReal_le_ofReal (hb i hh).1.le)
  have hv : μ univ < ⊤ := by
    rw [hx]; apply lt_of_le_of_lt (setLIntegral_mono' HV (g:=fun _ => ENNReal.ofReal 2) fun i hh => ENNReal.ofReal_le_ofReal (hb i hh).2.le)
    simp only [lintegral_const,Measure.restrict_apply_univ]
    apply ENNReal.mul_lt_top (by simp)
    exact lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall _ _).measure_lt_top
  letI : IsFiniteMeasure μ := ⟨hv⟩
  let g := G.probHaar U/μ univ
  have hz : g < ⊤ := ENNReal.div_lt_top (measure_ne_top G.probHaar U) hm
  have ht : 0 < g := ENNReal.div_pos (hg.1.measure_pos G.probHaar ⟨1,hu⟩).ne' hv.ne
  let k := g.toReal
  have hk : 0 < k := ENNReal.toReal_pos ht.ne' hz.ne
  refine ⟨⟨spin G,k,a⟩,hk,hy,hg.2.2.1.injOn,hi,he,fun x _ => spin_deriv G x,hp.measurable, ?_,hg.1⟩
  dsimp only; apply Measure.ext; intro A HA
  have HF := G.lieExp_cont.measurable
  rw [Measure.map_apply HF HA, Measure.restrict_apply HA,withDensity_apply _ (HF HA),Measure.restrict_restrict (HF HA)]
  simp_rw [ENNReal.ofReal_mul hk.le, lintegral_const_mul _ (hp.measurable.ennreal_ofReal)]
  rw [← bud_e G s HA,show ENNReal.ofReal k=g from ENNReal.ofReal_toReal hz.ne]
  change g * μ A = G.probHaar (A ∩ U)
  have HT : μ univ * G.probHaar (A∩U)= G.probHaar U * μ (A∩U) := roll G μ U _ HU (HA.inter HU) (bud_hit G U s hg hu (fun x h => (hi x h).le) (HA.inter HU) inter_subset_right)
  have Hm : μ (A∩U)=μ A := by
    unfold μ
    rw [bud_e G s (HA.inter HU),bud_e G s HA,show G.lieExp ⁻¹' (A∩U) ∩ s=G.lieExp ⁻¹' A ∩ s by
      ext; simp only [mem_preimage,mem_inter_iff]; exact ⟨fun hh => ⟨hh.1.1,hh.2⟩,fun hh => ⟨⟨hh.1,hg.2.2.2.2.2.1 hh.2⟩,hh.2⟩⟩]
  rw [Hm] at HT
  calc
    _ = G.probHaar U * μ A/(μ univ) := by unfold g; simp only [div_eq_mul_inv]; ring
    _ = _ := ((ENNReal.eq_div_iff hm hv.ne).2 HT).symm
end YM.LocalH
