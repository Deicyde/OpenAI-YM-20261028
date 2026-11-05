import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! L1 hol test for components. Can change real frames *at each* parameter when finding
     the L1 estimates. Need no common dominating functions across the disk. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Complex Set Filter Metric Topology Function MeasureTheory
open scoped BigOperators NNReal ENNReal Classical
variable {A : Type*} [MeasurableSpace A] {μ : Measure A} {E : Type*} [NormedAddCommGroup E]

lemma circle_meas [SFinite μ] (ν : Measure ℝ) [SFinite ν] {f : ℝ → A → E}
    (hc : ∀ a,Continuous fun t=> f t a) (hm : ∀ t,AEStronglyMeasurable (f t) μ) : AEStronglyMeasurable (uncurry f) (ν.prod μ) := by
  let k := (show StronglyMeasurable (id : ℝ→ℝ) from stronglyMeasurable_id)
  let g n (p:ℝ×A):= f (k.approx n p.1) p.2
  refine aestronglyMeasurable_of_tendsto_ae atTop (f:=g) (fun n=>?_) (Eventually.of_forall ?_)
  · let J:= k.approx n
    have hz : g n= fun p=> ∑ t∈J.range, ((fun x:ℝ×A=>J x.1)⁻¹'{t}).indicator (fun y:ℝ×A=> f t y.2) p := by
      ext p; rw [Finset.sum_eq_single (J p.1)]
      · rw [Set.indicator_of_mem]; exact rfl
      · intro i hi he; apply indicator_of_notMem; exact fun h=> he (show _=i from h).symm
      simp
    rw [hz]; exact Finset.aestronglyMeasurable_fun_sum _ (fun i _=> ((hm i).comp_snd).indicator ((J.measurable.comp measurable_fst) (measurableSet_singleton _)))
  rintro ⟨x,t⟩; exact ((hc t).tendsto x).comp (k.tendsto_approx x)

variable [NormedSpace ℂ E] [CompleteSpace E]

lemma local_major [SFinite μ] {F : ℂ → A → E} {r : ℝ} {c : ℂ} {M : ℝ} (hr : 0<r)
    (h : ∀ a:A,DifferentiableOn ℂ (fun z=>F z a) (closedBall c r))
    (hm : ∀ t∈sphere c r,Integrable (F t) μ) (hM : ∀ t∈sphere c r,∫ a, ‖F t a‖ ∂μ ≤ M) :
    ∃ b: A → ℝ, Integrable b μ ∧ ∀ t∈ball c (r/2),∀ a:A, ‖F t a‖ ≤ b a := by
  let R := circleMap c r; have hR x : R x∈ sphere c r:=circleMap_mem_sphere c hr.le _
  have hp : 0≤ 2*Real.pi:=by positivity
  let n := (volume : Measure ℝ).restrict (Ioc 0 (2*Real.pi)); letI : IsFiniteMeasure n:= by unfold n; infer_instance
  have hc a : Continuous fun x=> F (R x) a := by
    rw [← continuousOn_univ]; exact (h a).continuousOn.comp (continuous_circleMap ..).continuousOn (fun x _=>sphere_subset_closedBall (hR x))
  have hh : Integrable (fun x: ℝ × A=> F (R x.1) x.2) (n.prod μ) := by
    have he := circle_meas n (f:=fun t a=> F (R t) a) hc (fun t=> (hm _ (hR t)).1)
    apply (integrable_prod_iff he).2; refine ⟨Eventually.of_forall (fun x=> hm _ (hR x)),?_⟩
    apply (integrable_const M).mono' he.norm.integral_prod_right'
    filter_upwards with t; change ‖∫ a, ‖F _ a‖ ∂μ‖ ≤ _; rw [Real.norm_of_nonneg (integral_nonneg fun i=> norm_nonneg _)]; exact hM _ (hR t)
  let w:ℂ := (2*Real.pi*Complex.I:ℂ)
  refine ⟨fun a=> ‖w⁻¹‖*(2*(∫ t, ‖F (R t) a‖ ∂n)),(hh.integral_norm_prod_right.const_mul 2).const_mul _,fun z hz a=>?_⟩
  have hz' := (ball_subset_ball (half_le_self hr.le)) hz
  have he : w⁻¹ • (∫ t, deriv R t • ((R t-z)⁻¹ • F (R t) a) ∂n)=F z a := by
    obtain he:= (h a).circleIntegral_sub_inv_smul hz'; unfold circleIntegral at he; rw [intervalIntegral.integral_of_le hp] at he
    rw [show (∫ t, _ ∂n)= w • F z a from he]; exact inv_smul_smul₀ two_pi_I_ne_zero _
  rw [← he,norm_smul]; refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_) (norm_nonneg _)
  rw [← integral_const_mul]
  have hP t: r/2 ≤ ‖R t-z‖ := by
    have hk := dist_triangle (R t) z c; rw [mem_ball] at hz; rw [mem_sphere.mp (hR t),dist_eq_norm (R t) z] at hk; linarith
  have hQ t : R t-z ≠ 0 := norm_pos_iff.mp ((half_pos hr).trans_le (hP t))
  apply integral_mono
  · change IntegrableOn _ (Ioc (0:ℝ) (2*Real.pi)) volume
    refine (Continuous.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    refine Continuous.norm (Continuous.smul ?_ (Continuous.smul (((continuous_circleMap ..).sub continuous_const).inv₀ hQ) (hc a)))
    rw [show deriv R = _ from funext (deriv_circleMap c r)]; exact (continuous_circleMap ..).mul continuous_const
  · exact ((hc a).norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self).const_mul _
  intro t; dsimp only; rw [norm_smul,norm_smul, norm_inv, show deriv R t =_ from deriv_circleMap c r t,norm_mul,norm_I,mul_one, norm_circleMap_zero,abs_of_pos hr,← mul_assoc,← div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact (div_le_iff₀ (norm_pos_iff.mpr (hQ _))).2 (by linarith [hP t])

lemma tint [SFinite μ] {F : ℂ→ A → E} {s : Set ℂ} (hs : IsOpen s) {M : ℝ}
    (h : ∀ a:A,DifferentiableOn ℂ (fun z=>F z a) s) (hm : ∀ z∈s, Integrable (F z) μ)
    (hx : ∀ z∈s, ∫ a, ‖F z a‖ ∂μ ≤ M) : DifferentiableOn ℂ (fun z=> ∫ a, F z a ∂μ) s := by
  intro z hz
  obtain ⟨r,hr,hR⟩:= nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz); let d:= r/8; have hd : 0<d:= by unfold d; positivity
  obtain ⟨b,hb,hB⟩ := local_major hr (fun i=> (h i).mono hR) (fun y hy=>hm y (hR (sphere_subset_closedBall hy))) (fun y hy=> hx y (hR (sphere_subset_closedBall hy)))
  let D x a:= deriv (fun z=>F z a) x; have hp x (hp:x∈ball z d) : closedBall x d ⊆ ball z (r/2):= by
    intro y hy; rw [mem_closedBall] at hy; rw [mem_ball] at hp ⊢; have h:=dist_triangle y x z; unfold d at *; linarith
  have hw : ball z (r/2) ⊆ s:= ball_subset_closedBall.trans ((closedBall_subset_closedBall (half_le_self hr.le)).trans hR)
  have he x (hy:x∈ball z d) a : HasDerivAt (fun z=>F z a) (D x a) x := ((h a).differentiableAt (hs.mem_nhds (hw (hp x hy (mem_closedBall_self hd.le))))).hasDerivAt
  have hF : AEStronglyMeasurable (D z) μ := by
    let u:ℂ→ A → E:=fun w i=> if w∈s then (w-z)⁻¹ • (F w i-F z i) else 0
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] z) (f:=u) (fun w=>?_) (Eventually.of_forall ?_)
    · unfold u; split_ifs with hw
      · exact (((hm _ hw).1).sub (hm z hz).1).const_smul _
      exact aestronglyMeasurable_const
    intro i; refine (hasDerivAt_iff_tendsto_slope.mp (he z (mem_ball_self hd) i)).congr' ?_
    filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (hs.mem_nhds hz)] with z' hz'
    unfold u; rw [if_pos (show z'∈s from hz')]; rfl
  have hV : ∀ᵐ i ∂μ, ∀ x∈ball z d, ‖D x i‖≤ b i / d := Eventually.of_forall fun i x hh=> by
    unfold D; rw [← cderiv_eq_deriv hs (h i) hd ((hp x hh).trans hw)]; apply norm_cderiv_le hd; exact fun y hy=> hB y (hp x hh (sphere_subset_closedBall hy)) i
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z hd) ((show ∀ᶠ q in 𝓝 z,q∈s from hs.mem_nhds hz).mono fun q hq=> (hm q hq).1)
    (hm z hz) hF hV (hb.div_const _) (Eventually.of_forall fun i x hx=> he x hx i)).2.differentiableAt.differentiableWithinAt
end YM.UVExtension.Lamppost
