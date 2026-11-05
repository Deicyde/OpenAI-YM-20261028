import YM.TraceExtension.LaplaceDensity

/-! Continuity theorem for Laplace transform on the open future cone.
A convenient (Hausdorff moment style) Tauberian for our *positive*
measures. This module proves actual test-function implications from
all-future Laplace hypotheses, not a boundary-value heuristic. -/

set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension
open Function Set Filter MeasureTheory Measure Metric Mink Boundary
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical

structure AllowsLaplace (μ : Measure E4) : Prop where
    supports : μ coneᶜ=0
    accepts (u : E4) : u∈inside → IsFiniteMeasure (lag μ u)

lemma AllowsLaplace.members {μ : Measure E4} (h : AllowsLaplace μ) : ∀ᵐ p ∂μ, p∈cone := by rw [ae_iff]; exact h.supports

def decode (f : Sensor) (x : E4) := if h:x∈cone then f (OnePoint.some (⟨x,h⟩:cone)) else 0
lemma decode_cont (f : Sensor) : ContinuousOn (decode f) cone := by
    rw [continuousOn_iff_continuous_restrict];
    have hh (x:cone) : decode f x=f (OnePoint.some x) := by unfold decode; rw [dif_pos x.property]
    rw [show cone.restrict (decode f)=f ∘ OnePoint.some from funext hh]
    exact f.continuous.comp OnePoint.continuous_coe

lemma decode_int (f : Sensor) (μ : Measure E4) (h : AllowsLaplace μ) (u : inside) :
    Integrable (decode f) (lag μ u) := by
    haveI he : IsFiniteMeasure (lag μ u) := h.accepts _ u.property
    have hh : ∀ᵐ p ∂(lag μ u), p∈cone := h.members.filter_mono
      (Measure.AbsolutelyContinuous.ae_le (withDensity_absolutelyContinuous ..))
    apply (integrable_const ‖f‖).mono'
    · have he := (decode_cont f).aestronglyMeasurable (μ := lag μ u) closed_cone.measurableSet
      rwa [Measure.restrict_eq_self_of_ae_mem hh] at he
    filter_upwards [hh] with p hp; rw [decode,dif_pos hp]; exact ContinuousMap.norm_coe_le_norm ..

lemma decode_add (f g : Sensor) (μ : Measure E4) (h : AllowsLaplace μ) (u : inside) :
    (∫ p, decode (f+g) p ∂lag μ u) = (∫ p,decode f p ∂lag μ u) + ∫ p,decode g p ∂lag μ u := by
    rw [← integral_add (decode_int f _ h _) (decode_int g _ h _)]
    congr! 1; funext p; by_cases hp:p∈cone <;> simp [decode,hp]
lemma decode_mul (f : Sensor) (a : ℝ) (μ : Measure E4) (u : inside) :
    (∫ p, decode (a•f) p ∂lag μ u) = a * ∫ p,decode f p ∂lag μ u := by
    rw [← integral_const_mul]; congr! 1; funext p; by_cases hp:p∈cone <;> simp [decode,hp]
lemma decode_zero (μ : Measure E4) (u : inside) : (∫ p, decode 0 p ∂lag μ u) = 0 := by simp [decode]
lemma decode_cost (f g : Sensor) (μ : Measure E4) (h : AllowsLaplace μ) (u : inside) :
    dist (∫ p, decode f p ∂lag μ u) (∫ p, decode g p ∂lag μ u) ≤ (lag μ u).real univ*‖f-g‖ := by
    haveI he : IsFiniteMeasure (lag μ u) := h.accepts _ u.property
    rw [dist_eq_norm,← integral_sub (decode_int f _ h u) (decode_int g _ h u)]
    refine (norm_integral_le_of_norm_le (f:=fun p => decode f p-decode g p) (integrable_const ‖f-g‖) ?_).trans (by rw [integral_const]; rfl)
    filter_upwards with x; by_cases hp : x∈cone
    · unfold decode; rw [dif_pos hp,dif_pos hp]; exact ContinuousMap.norm_coe_le_norm (f-g) (OnePoint.some (⟨x,hp⟩:cone))
    simp [decode,hp]

lemma lag_eval (μ : Measure E4) (_h : AllowsLaplace μ) (u : inside) :
    (lag μ u).real univ=∫ p,Real.exp (-inner ℝ u.val p) ∂μ := by
    haveI he : IsFiniteMeasure (lag μ u) := _h.accepts _ u.property
    rw [show (lag μ u).real univ= ∫ _ : E4,(1:ℝ) ∂lag μ u from by simp,lag, integral_withDensity_eq_integral_smul (lagWeight_cont _).measurable]
    congr! 1; funext p; change (Real.exp _)*1=_; rw [mul_one]

lemma decode_one (μ : Measure E4) (h : AllowsLaplace μ) (u : inside) :
    (∫ p, decode 1 p ∂lag μ u) = (lag μ u).real univ := by
    rw [lag_eval μ h,lag,integral_withDensity_eq_integral_smul (lagWeight_cont _).measurable]
    apply integral_congr_ae; filter_upwards [h.members] with p hp
    unfold decode; rw [dif_pos hp]; change Real.exp _ * 1 = _; rw [mul_one]
lemma decode_sensor (v : inside) (μ : Measure E4) (h : AllowsLaplace μ) (u : inside) :
    (∫ p, decode (sensor v) p ∂lag μ u) = (lag μ (u.val+v.val)).real univ := by
    let r : inside := ⟨u.val+v.val,add_inside u.property v.property⟩
    rw [show lag μ (u.val+v.val)=lag μ r from rfl,lag_eval μ h r,lag,integral_withDensity_eq_integral_smul (lagWeight_cont _).measurable]
    apply integral_congr_ae; filter_upwards [h.members] with p hp
    unfold decode; rw [dif_pos hp]; change Real.exp _ * Real.exp _ = _
    change Real.exp (-inner ℝ u.val p)*Real.exp (-inner ℝ v.val p) = Real.exp (-inner ℝ (u.val+v.val) p)
    rw [← Real.exp_add,inner_add_left,neg_add]

variable {ι : Type*} {l : Filter ι} (μ : ι → Measure E4) (ν : Measure E4)
    (hf : ∀ᶠ i in l, AllowsLaplace (μ i)) (hν : AllowsLaplace ν)
    (hx : ∀ (u : inside), Tendsto (fun i => lag (μ i) u univ) l (𝓝 (lag ν u univ)))
include hν hx
lemma limit_real (u : inside) : Tendsto (fun i => (lag (μ i) u).real univ) l (𝓝 ((lag ν u).real univ)) := by
    haveI he := hν.accepts u u.property; exact (ENNReal.tendsto_toReal (measure_ne_top (lag ν u) _)).comp (hx u)

include hf
lemma laplace_algebra {f : Sensor} (h : f∈Submodule.span ℝ scanner) (u : inside) :
    Tendsto (fun i => ∫ p,decode f p ∂lag (μ i) u) l (𝓝 (∫ p, decode f p ∂lag ν u)) := by
    induction h using Submodule.span_induction with
    | mem f h =>
      rcases h with h|⟨a,rfl⟩
      · rw [h, decode_one ν hν u]; refine (limit_real μ ν hν hx u).congr' ?_
        filter_upwards [hf] with i hi using (decode_one (μ i) hi _).symm
      rw [decode_sensor a ν hν u]; refine (limit_real μ ν hν hx (⟨u.val + a.val, add_inside u.property a.property⟩ : inside)).congr' ?_
      filter_upwards [hf] with i hi using (decode_sensor a (μ i) hi u).symm
    | zero => simp_rw [decode_zero]; exact tendsto_const_nhds
    | add f g _ _ h h' =>
      rw [decode_add f g ν hν u]; apply (h.add h').congr'
      filter_upwards [hf] with i hi using (decode_add f g (μ i) hi _).symm
    | smul a f h ih =>
      simp_rw [decode_mul f a]; exact ih.const_mul _

lemma laplace_continuous (f : Sensor) (u : inside) :
    Tendsto (fun i => ∫ p,decode f p ∂lag (μ i) u) l (𝓝 (∫ p, decode f p ∂lag ν u)) := by
    apply Metric.tendsto_nhds.mpr; intro ε he
    let b := (lag ν u).real univ+1
    have hb : 0<b := add_pos_of_nonneg_of_pos measureReal_nonneg zero_lt_one
    obtain ⟨x,hx',hh⟩ := scan_dense f (ε:=ε/(3*b)) (by positivity)
    have hc : b*‖x-f‖<ε/3 := by
      have hu := (lt_div_iff₀ (by positivity : 0<3*b)).mp hh; linarith
    have ht : (lag ν u).real univ < b := lt_add_one _
    filter_upwards [(limit_real μ ν hν hx u).eventually (gt_mem_nhds ht),hf,
      Metric.tendsto_nhds.mp (laplace_algebra μ ν hf hν hx hx' u) (ε/3) (by positivity)] with i hi hi' hB
    let g (f : Sensor) (μ : Measure E4) := ∫ p,decode f p ∂lag μ u
    change dist (g f _) (g f _) < _
    refine lt_of_le_of_lt (dist_triangle4 (g f (μ i)) (g x (μ i)) (g x ν) (g f ν)) ?_
    have hy : dist (g f (μ i)) (g x (μ i)) < ε/3 := by
        rw [dist_comm]
        exact lt_of_le_of_lt ((decode_cost x f (μ i) hi' _).trans (mul_le_mul_of_nonneg_right (show (lag (μ i) u).real univ ≤ b from le_of_lt hi) (norm_nonneg _))) hc
    have hv : dist (g x ν) (g f ν) < ε/3 :=
        lt_of_le_of_lt ((decode_cost x f ν hν _).trans (mul_le_mul_of_nonneg_right ht.le (norm_nonneg _))) hc
    change dist (g x _) (g x _)<_ at hB; linarith

omit hf hν hx in
lemma decode_compact (f : E4 → ℝ) (hc : Continuous f) (hp : HasCompactSupport f) (u : E4) : ∃ x : Sensor, EqOn (decode x) (fun v => Real.exp (inner ℝ u v)*f v) cone := by
    let g : C(↥cone,ℝ) := ⟨fun v => Real.exp (inner ℝ u v.val)*f v.val,by fun_prop⟩
    have hh : Tendsto g (coclosedCompact cone) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [lid_escape.eventually hp.compl_mem_cocompact] with p h
      change 0=Real.exp _ * _; rw [image_eq_zero_of_notMem_tsupport h,mul_zero]
    refine ⟨OnePoint.continuousMapMk g 0 hh,fun v hv => ?_⟩; unfold decode; rw [dif_pos hv]; rfl

omit hf hν hx in
lemma compact_evaluation {f : E4 → ℝ} {u : inside} {x : Sensor} (h : EqOn (decode x) (fun v => Real.exp (inner ℝ u.val v)*f v) cone) (μ : Measure E4) (ht : AllowsLaplace μ) : (∫ p,decode x p ∂lag μ u) = (∫ p,f p ∂μ) ∧ Integrable f μ := by
    have he : (fun p : E4 => (lagWeight u p) • decode x p) =ᵐ[μ] f := by
         filter_upwards [ht.members] with p hp
         rw [h hp]; change Real.exp (-inner ℝ u.val p)*(Real.exp _*f p)=_
         rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
    refine ⟨?_, ((integrable_withDensity_iff_integrable_smul (lagWeight_cont _).measurable).1 (decode_int x μ ht u)).congr he⟩
    · rw [lag,integral_withDensity_eq_integral_smul (lagWeight_cont _).measurable]; exact integral_congr_ae he

omit hf hν hx in
theorem integrable_sensor {κ : Measure E4} (hk : AllowsLaplace κ) (f : E4 → ℝ) (hc : Continuous f) (hp : HasCompactSupport f) : Integrable f κ := by
    obtain ⟨x,h⟩ := decode_compact f hc hp (basis timeAxis)
    exact (compact_evaluation (u:=⟨_,clock_inside⟩) h κ hk).2

theorem laplace_compact (f : E4 → ℝ) (hc : Continuous f) (hp : HasCompactSupport f) :
    Tendsto (fun i => ∫ p,f p ∂μ i) l (𝓝 (∫ p,f p ∂ν)) := by
    let u : inside := ⟨_,clock_inside⟩
    obtain ⟨x,h⟩ := decode_compact f hc hp u
    rw [← (compact_evaluation (u:=u) h ν hν).1]
    apply (laplace_continuous μ ν hf hν hx x u).congr'
    filter_upwards [hf] with i hi using (compact_evaluation h (μ i) hi).1
end YM.TraceExtension
