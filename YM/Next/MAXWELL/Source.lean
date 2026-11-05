import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Next.MAXWELL.Pole



/-!
# Positive smooth regulator for the free potential

On genuine 4D Lebesgue volume. Its **minus** Laplacian is a unit
approximate delta. A tool for keeping the normalization of the stress
flux, not an assertion of contacts in any continuum hierarchy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

/-- t>0. At 0 we'll only use the germ at nonzero x. -/
def soften (t : ℝ) (x : E4) : ℝ := normal * (t^2 + ‖x‖^2)⁻¹

def source (t : ℝ) (x : E4) : ℝ := 8 * normal * t^2 * (t^2 + ‖x‖^2)⁻¹^3

lemma soften_zero : soften 0 = Green := funext fun x => by simp [soften,Green]

lemma soften_diff {t : ℝ} (ht : 0 < t) : ContDiff ℝ ω (soften t) :=
  contDiff_const.mul ((contDiff_const.add (contDiff_norm_sq ℝ)).inv (show ∀ x : E4, t^2 + ‖x‖^2 ≠ 0 from fun x => by positivity))

lemma source_diff {t : ℝ} (ht : 0 < t) : ContDiff ℝ ω (source t) :=
  contDiff_const.mul (((contDiff_const.add (contDiff_norm_sq ℝ)).inv (show ∀ x : E4, t^2 + ‖x‖^2 ≠ 0 from fun x => by positivity)).pow _)

lemma soften_first {t : ℝ} {x : E4} (ht : t^2+‖x‖^2 ≠ 0) (i : Axis) :
    grad i (soften t) x = -2 * normal * x i * (t^2+‖x‖^2)⁻¹^2 := by
  have h := ((hasFDerivAt_inv ht).comp x
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add (t^2))).const_mul normal
  have he := h.fderiv; change fderiv ℝ (soften t) x = _ at he
  unfold grad D; rw [he]; simp [← real_inner_comm x]; ring

lemma soften_second {t : ℝ} {x : E4} (ht : t^2+‖x‖^2 ≠ 0) (i j : Axis) :
    grad i (grad j (soften t)) x = -2 * normal * basis i j * (t^2+‖x‖^2)⁻¹^2 +
      8 * normal * x i * x j * (t^2+‖x‖^2)⁻¹^3 := by
  have he : grad j (soften t) =ᶠ[𝓝 x] fun y => -2 * normal * y j * (t^2+‖y‖^2)⁻¹^2 := by
    have hc : Continuous fun y : E4 => t^2 + ‖y‖^2 := by fun_prop
    filter_upwards [hc.continuousAt.eventually_ne ht] with y hy; exact soften_first hy j
  change D (basis i) _ _ = _
  rw [GermD _ he]
  have h := (((compAxis j).hasFDerivAt (x := x)).const_mul (-2 * normal)).mul
    (((hasFDerivAt_inv ht).comp x ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add (t^2))).pow 2)
  have hw := h.fderiv; change fderiv ℝ (fun y : E4 => -2 * normal * y j * (t^2+‖y‖^2)⁻¹^2) x = _ at hw
  rw [D, hw]; simp [-basis_eq, compAxis, ← real_inner_comm x]; field_simp
  ring

lemma minus_lap {t : ℝ} (h : 0 < t) : lap (soften t) = -source t := by
  funext x
  have ht : 0 < t^2+‖x‖^2 := by positivity
  simp only [lap,soften_second (t:=t) (x:=x) ht.ne',basis_eq,↓reduceIte,mul_one,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat]
  rw [← Finset.sum_mul]
  simp_rw [mul_assoc (8*normal),← sq, ← Finset.mul_sum]
  rw [← EuclideanSpace.real_norm_sq_eq,Pi.neg_apply,source]
  field_simp; ring



lemma source_scale {t : ℝ} (h : 0 < t) (x : E4) : t^4 * source t (t • x) = source 1 x := by
  unfold source; rw [norm_smul,Real.norm_eq_abs, abs_of_pos h]
  field_simp

private theorem profile_bill : IntegrableOn (fun r : ℝ => r^3*(1+r^2)⁻¹^3) (Ioi 0) ∧
    (∫ r in Ioi (0:ℝ), r^3*(1+r^2)⁻¹^3) = 1/4 := by
  let g := fun x : ℝ => (1-(1+x^2)⁻¹)^2/4
  have hn (x : ℝ) : 0 < 1+x^2 := by positivity
  have hp (x : ℝ) : HasDerivAt g (x^3*(1+x^2)⁻¹^3) x := by
    unfold g
    refine ((((hasDerivAt_id' x).pow 2).const_add 1 |>.inv (hn x).ne').const_sub 1 |>.pow 2 |>.div_const 4).congr_deriv ?_
    simp only [Pi.inv_apply,Pi.pow_apply]
    field_simp
    ring_nf
    field_simp
  have hw (x : ℝ) (hx : x ∈ Ioi (0:ℝ)) : 0 ≤ x^3*(1+x^2)⁻¹^3 := by have : 0 < x := hx; positivity
  have he : Tendsto g atTop (𝓝 (1/4)) := by
    have h₁ : Tendsto (fun x : ℝ => (1+x^2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (show (fun x : ℝ => x^2) ≤ fun x => 1+x^2 from
        fun x => le_add_of_nonneg_left zero_le_one) (tendsto_pow_atTop (by omega)))
    simpa [g] using (((h₁.const_sub 1).pow 2).div_const (4:ℝ))
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hp x) hw he,?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => hp x) hw he]; simp [g]

theorem source_profile : Integrable (source 1) ∧ (∫ x : E4, source 1 x) = 1 := by
  let f := fun r : ℝ => 8 * normal * (1:ℝ)^2 * (1^2+r^2)⁻¹^3
  have he := profile_bill
  have hd : Module.finrank ℝ E4 = 4 := by simp
  have h (r : ℝ) : r^(Module.finrank ℝ E4-1) • f r = (8*normal)*(r^3*(1+r^2)⁻¹^3) := by
    rw [hd]; dsimp only [f]; simp; ring
  change Integrable (fun (x:E4) => f ‖x‖) ∧ _
  refine ⟨(integrable_fun_norm_addHaar volume).mpr ?_, ?_⟩
  · simp_rw [h]; exact he.1.const_mul _
  have ht : volume.real (Metric.ball (0:E4) 1) = Real.pi^2/2 := by
    rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even (k:=2) (by simp [hd]),ENNReal.ofReal_one,one_pow,one_mul,
      ENNReal.toReal_ofReal (by positivity)]; norm_num
  change (∫ x : E4, f ‖x‖) = 1
  rw [integral_fun_norm_addHaar]; simp_rw [h]; rw [integral_const_mul,he.2,ht,hd]
  simp only [normal, nsmul_eq_mul,smul_eq_mul,Nat.cast_ofNat]; field_simp
  ring

/-- Useful affine change of variable on volume (does not assume integrability). -/
lemma dilate_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (F₀ : E4 → F) (x : E4) (t : ℝ)
    (h : 0 < t) : (∫ y, F₀ y) = t^4 • ∫ y : E4, F₀ (x+t • y) := by
  calc
    _ = ∫ y, F₀ (x+y) := (integral_add_left_eq_self F₀ x).symm
    _ = _ := by
      rw [show (fun y => F₀ (x+t • y)) = (fun y => (fun z => F₀ (x+z)) (t • y)) from rfl]
      rw [MeasureTheory.Measure.integral_comp_smul_of_nonneg volume (fun z => F₀ (x+z)) t (hR := h.le)]
      rw [show Module.finrank ℝ E4=4 by simp, smul_inv_smul₀ (by positivity : t^4 ≠ 0)]

lemma testing_source {f : E4 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (x : E4) :
    Tendsto (fun t => ∫ y : E4, source t (y-x) * f y) (𝓝[>] (0:ℝ)) (𝓝 (f x)) := by
  have he t (ht : 0 < t) : (∫ y : E4, source t (y-x) * f y) = ∫ y : E4, source 1 y * f (x+t • y) := by
    rw [dilate_integral (fun y => source t (y-x) * f y) x t ht, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_); simp only [add_sub_cancel_left,smul_eq_mul, ← mul_assoc,source_scale ht]
  obtain ⟨C,hC⟩ := hf.bounded_above_of_compact_support hc
  have hv : (∫ y : E4, source 1 y * f x) = f x := by rw [integral_mul_const, source_profile.2,one_mul]
  refine Tendsto.congr' ?_ (show Tendsto (fun t : ℝ => ∫ y : E4, source 1 y * f (x+t • y)) _ _ from ?_)
  · filter_upwards [self_mem_nhdsWithin] with t ht; exact (he t ht).symm
  rw [← hv]
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖source 1 y‖ * C) _ _
    (source_profile.1.norm.mul_const C)
  · refine Eventually.of_forall fun y => ?_
    have hg : Continuous (fun t : ℝ => source 1 y * f (x+t • y)) := by fun_prop
    simpa using (hg.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  · exact Eventually.of_forall fun t => ((source_diff (by norm_num : (0:ℝ)<1)).continuous.mul
      (hf.comp (show Continuous fun y : E4 => x+t • y by fun_prop))).aestronglyMeasurable
  refine Eventually.of_forall fun t => Eventually.of_forall fun y => ?_
  change ‖source 1 y * f (x+t • y)‖ ≤ ‖_‖ * _
  rw [norm_mul]; gcongr; exact hC _

end YM.Maxwell.Free
