import YM.Next.FOUNDATIONS.SU2
import YM.Push.BETA_TRANSPORT.Noise

/-!
# β derivative of RG.StepData.push

Against unaltered probability Haar priors. These estimates handle *every*
slice V with no null exceptional V, and include L¹-costs on the derivative
and the scale/period-explicit cost of the kernel. Do not interpolate between
branch decisions as β moves. Signed transformations and gauge transformations
of the derivative use the very same calendar as the kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG Pressure Gibbs MeasureTheory Filter Set
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {c f : Side} (S : StepData c f) {G : Gauge}

def densitySlope (β : ℝ) (U : Config G f) (V : Config G c) := ∑ t, tagSlope S β t U V

lemma density_bounds (h : S.patch.Branches S.kernel G) {β R : ℝ} (hβ : |β| ≤ R) (U : Config G f) (V) :
    (noiseCost S R)⁻¹ ≤ S.density β U V ∧ S.density β U V ≤ noiseCost S R := by
  have he (b : ℝ) : ∑ t, S.likelihood U t * b = b := by rw [← Finset.sum_mul, S.chosen h,one_mul]
  exact ⟨(he _).symm.trans_le (Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (noise_bounds S hβ _ V).1
    (S.likelihood_pos _ t)), (Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (noise_bounds S hβ _ V).2
    (S.likelihood_pos _ t)).trans_eq (he _)⟩



lemma density_hasDerivAt (β : ℝ) (U : Config G f) (V : Config G c) :
    HasDerivAt (S.density · U V) (densitySlope S β U V) β :=
  HasDerivAt.fun_sum fun t _ => tag_hasDerivAt S β t U V

lemma density_estimate (h : S.patch.Branches S.kernel G) :
    WeightEstimate (fun β (p : Config G f × Config G c) => S.density β p.1 p.2)
      (fun β p => densitySlope S β p.1 p.2) (noiseCap S) (noiseCost S) := by
  refine ⟨S.density_meas h,fun β => Finset.measurable_fun_sum _ fun t _ => (tag_estimate S h t).measurable' β,
    fun _ p => S.density_positive ..,fun hb p => (density_bounds S h hb _ _).2, fun β p => ?_,
    fun _ p => density_hasDerivAt ..,noiseCap_nonneg _,fun R _ => (noiseCost_pos S R).le⟩
  unfold StepData.density densitySlope
  rw [Finset.mul_sum]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun _ _ => tagSlope_bound ..)

lemma slice_estimate (h : S.patch.Branches S.kernel G) (V : Config G c) :
    WeightEstimate (fun β U => S.density β U V) (fun β U => densitySlope S β U V) (noiseCap S) (noiseCost S) :=
  (density_estimate S h).comp (f:=fun x => (x,V)) (measurable_id.prodMk measurable_const)

lemma density_cont_all (U : Config G f) : Continuous fun p : ℝ × Config G c => S.density p.1 U p.2 := by
  unfold StepData.density
  exact continuous_finsetSum _ fun t _ => continuous_const.mul ((noise_cont_all S).comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))

@[simp] lemma density_zero (h : S.patch.Branches S.kernel G) (U : Config G f) (V) : S.density 0 U V = 1 := by
  simpa only [StepData.density, noise_zero, mul_one] using S.chosen h U







variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def pushSlope (β : ℝ) (F : Config G f → X) (V : Config G c) :=
  ∫ U, densitySlope S β U V • F U ∂prior G f



lemma pushSlope_integrand (h : S.patch.Branches S.kernel G) {F : Config G f → X} (hf : Integrable F (prior G f))
    (β : ℝ) : Integrable (fun p : Config G f × Config G c => densitySlope S β p.1 p.2 • F p.1)
      ((prior G f).prod (prior G c)) :=
  (density_estimate S h).slope_integrable _ (hf.comp_fst _)

lemma pushSlope_integrable (h : S.patch.Branches S.kernel G) {F : Config G f → X} (hf : Integrable F (prior G f))
    (β : ℝ) : Integrable (pushSlope S β F) (prior G c) := (pushSlope_integrand S h hf β).integral_prod_right

-- Keep Bochner completeness.
set_option linter.unusedSectionVars false
variable [CompleteSpace X]





lemma pushSlope_norm_le (h : S.patch.Branches S.kernel G) {F : Config G f → X} (hf : Integrable F (prior G f))
    (V : Config G c) (β : ℝ) : ‖pushSlope S β F V‖ ≤ noiseCap S * S.push β (fun U => ‖F U‖) V :=
  (slice_estimate S h V).slope_integral_le β hf





lemma push_continuousWithinAt (h : S.patch.Branches S.kernel G) {Y : Type*} [TopologicalSpace Y]
    [FirstCountableTopology Y] {b : Y → ℝ} {s : Set Y} {y : Y} {F : Y → Config G f → X} {V : Y → Config G c}
    (hb : ContinuousWithinAt b s y) (hv : ContinuousWithinAt V s y) (hi : Integrable (F y) (prior G f))
    (hm : ∀ᶠ z in 𝓝[s] y, AEStronglyMeasurable (F z) (prior G f))
    (hc : ∀ᵐ x ∂prior G f, ContinuousWithinAt (F · x) s y) {M : Config G f → ℝ} (hM : Integrable M (prior G f))
    (he : ∀ᶠ z in 𝓝[s] y, ∀ᵐ x ∂prior G f, ‖F z x‖ ≤ M x) :
    Integrable (fun x => S.density (b y) x (V y) • F y x) (prior G f) ∧
      ContinuousWithinAt (fun z => S.push (b z) (F z) (V z)) s y := by
  refine ⟨(slice_estimate S h _).smul_integrable _ hi,tendsto_integral_filter_of_dominated_convergence
    (fun x => noiseCost S (|b y|+1) * M x)
    (hm.mono fun z hz => ((slice_estimate S h (V z)).measurable _).aestronglyMeasurable.smul hz) ?_
    (hM.const_mul _) (hc.mono fun x hx => ?_)⟩
  · filter_upwards [hb (eventually_abs_bound _),he] with z hz he'
    filter_upwards [he'] with x hx
    rw [norm_smul]; exact mul_le_mul ((slice_estimate S h _).nonneg _ _ |> Real.norm_of_nonneg |>.trans_le
      ((slice_estimate S h _).le hz x)) hx (norm_nonneg _) (noiseCost_pos ..).le
  exact ((density_cont_all S x).continuousAt.tendsto.comp (hb.prodMk_nhds hv)).smul hx

@[simp] lemma push_zero (h : S.patch.Branches S.kernel G) (F : Config G f → X) (V) :
    S.push 0 F V = ∫ U, F U ∂prior G f := by simp [StepData.push,density_zero S h]
end YM.Push.BetaTransport
