import YM.RG.Measurable
import Mathlib.MeasureTheory.Integral.Pi

/-!
Conditional kernel lemmas.

This component NEVER
chooses another offset, new cutoffs, or divides each source by a
configuration-dependent density.

Even winding reads share choices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG

open MeasureTheory Set Lattice Wilson
open scoped Topology Matrix.Norms.Frobenius ENNReal

/-- One coarse graining step, fine to coarse. -/
structure StepData (c f : Side) where
  patch : Patch
  kernel : KernelChoices
  sizes : f.val = c.val * patch.L.val

namespace StepData
variable {c f : Side} (S : StepData c f) {G : Gauge}

def ratio : Ratio c f := ⟨S.patch.L, S.sizes⟩

abbrev SitesChoice := Site c → S.patch.FrameTag
abbrev BondChoice := Edge (Site c) → S.patch.Points
abbrev Choices := S.SitesChoice × S.BondChoice

def frames (U : Config G f) (t : S.SitesChoice) (x : Site c) : S.patch.Frame G :=
  S.patch.frame S.kernel (expandAt (S.ratio.embed x) U) (t x)

def connector (U : Config G f) (t : S.SitesChoice) (e : Edge (Site c)) : S.patch.Connector G := fun x =>
  S.frames U t e.1 x *
    travel (expandAt (S.ratio.embed e.1) U) x.val (List.replicate S.patch.L.val (posDir e.2)) *
    (S.frames U t (e.1 + Lattice.step e.2) x)⁻¹

def prediction (U : Config G f) (t : S.Choices) : Config G c := fun e =>
  S.patch.predict S.kernel (S.connector U t.1 e) (t.2 e)

/-- Actual joint probability of physical site and bond tags, unused tags
included with uniform mass. -/
def likelihood (U : Config G f) (t : S.Choices) : ℝ :=
  (∏ x, S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) U) (t.1 x)) *
    ∏ e, S.patch.predictorMass S.kernel (S.connector U t.1 e) (t.2 e)

def penaltyWeight (β : ℝ) (v : G.El) := Real.exp (-β * S.kernel.penalty * G.price v)

theorem penaltyWeight_cont (β : ℝ) : Continuous (S.penaltyWeight (G := G) β) := by
  unfold penaltyWeight; fun_prop

def penaltyZ (β : ℝ) (G : Gauge) := ∫ v : G.El, S.penaltyWeight β v ∂G.probHaar

theorem penaltyZ_pos (β : ℝ) : 0 < S.penaltyZ β G := by
  have h (v : G.El) : 0 < S.penaltyWeight β v := Real.exp_pos _
  have hi : Integrable (S.penaltyWeight β) G.probHaar :=
    (S.penaltyWeight_cont β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply (integral_pos_iff_support_of_nonneg (fun v => (h v).le) hi).2
  rw [show Function.support (S.penaltyWeight β (G := G)) = univ from Set.eq_univ_of_forall fun v ↦ (h v).ne']
  simp

def noise (β : ℝ) (Q V : Config G c) :=
  ∏ b, (S.penaltyZ β G)⁻¹ * S.penaltyWeight β (V b * (Q b)⁻¹)

def density (β : ℝ) (U : Config G f) (V : Config G c) :=
  ∑ t, S.likelihood U t * S.noise β (S.prediction U t) V

/-- The push of unnormalized functions (proof of integrability of input required in applications).
Output is a function against the *probability Haar* prior at the coarse level.
-/
def push {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (β : ℝ) (F : Config G f → X) (V : Config G c) :=
  ∫ U : Config G f, S.density β U V • F U ∂(prior G f)

private theorem expand_cont (x : Site f) : Continuous fun U : Config G f => expandAt x U := by
  unfold expandAt; fun_prop

theorem frames_meas (h : S.patch.Branches S.kernel G) (t : S.SitesChoice) (x : Site c) :
    Measurable fun U : Config G f => S.frames U t x :=
  (S.patch.frame_meas h _).comp (expand_cont _).measurable

theorem connector_meas (h : S.patch.Branches S.kernel G) (t : S.SitesChoice) (e : Edge (Site c)) :
    Measurable fun U : Config G f => S.connector U t e := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  have hc : Measurable fun U : Config G f => S.frames U t e.1 i :=
    (measurable_pi_apply _).comp (S.frames_meas h t _)
  have hd : Measurable fun U : Config G f => S.frames U t (e.1+step e.2) i :=
    (measurable_pi_apply _).comp (S.frames_meas h t _)
  let p := List.replicate S.patch.L.val (posDir e.2)
  have he : Measurable fun U : Config G f => travel (expandAt (S.ratio.embed e.1) U) i.val p :=
    ((continuous_travel _ _).comp (expand_cont _)).measurable
  exact (hc.mul he).mul hd.inv

theorem prediction_meas (h : S.patch.Branches S.kernel G) (t : S.Choices) :
    Measurable fun U : Config G f => S.prediction U t := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact (S.patch.predict_meas h _).comp (S.connector_meas h t.1 i)

theorem likelihood_meas (h : S.patch.Branches S.kernel G) (t : S.Choices) :
    Measurable fun U : Config G f => S.likelihood U t := by
  unfold likelihood
  apply Measurable.mul
  · refine Finset.measurable_fun_prod _ fun i _ ↦ ?_
    exact (S.patch.frameMass_meas _).comp (expand_cont _).measurable
  · refine Finset.measurable_fun_prod _ fun i _ ↦ ?_
    exact (S.patch.predictorMass_meas _).comp (S.connector_meas h t.1 i)

theorem likelihood_pos (U : Config G f) (t : S.Choices) : 0 ≤ S.likelihood U t := by
  apply mul_nonneg
  · apply Finset.prod_nonneg; intro _ _; unfold Patch.frameMass; split
    · positivity
    split <;> positivity
  · apply Finset.prod_nonneg; intro _ _; unfold Patch.predictorMass; split
    · positivity
    exact S.patch.weight_nonneg _

theorem chosen (h : S.patch.Branches S.kernel G) (U : Config G f) : ∑ t, S.likelihood U t = 1 := by
  let a (r : S.SitesChoice) := ∏ x, S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) U) (r x)
  let b (r : S.SitesChoice) (t : S.BondChoice) :=
    ∏ e, S.patch.predictorMass S.kernel (S.connector U r e) (t e)
  have ha : ∑ i, a i = 1 := by
    unfold a
    rw [← Fintype.prod_sum]
    simp_rw [S.patch.frameMass_sum h]; simp
  have hb (r) : ∑ i, b r i = 1 := by
    unfold b
    rw [← Fintype.prod_sum]; simp_rw [S.patch.predictorMass_sum]; simp
  rw [Fintype.sum_prod_type]
  change ∑ i, ∑ t, a i * b i t = _
  simp_rw [← Finset.mul_sum, hb, mul_one]; exact ha

theorem noise_cont (β : ℝ) : Continuous fun x : Config G c × Config G c => S.noise β x.1 x.2 := by
  unfold noise penaltyWeight
  fun_prop

theorem noise_integrable (β : ℝ) (Q : Config G c) : Integrable (S.noise β Q) (prior G c) :=
  ((S.noise_cont β).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem noise_mass (β : ℝ) (Q : Config G c) :
    (∫ V, S.noise β Q V ∂prior G c) = 1 := by
  have he (b : G.El) : (∫ u : G.El, (S.penaltyZ β G)⁻¹ * S.penaltyWeight β (u * b⁻¹) ∂G.probHaar) = 1 := by
    have h := (measurePreserving_mul_right G.probHaar b⁻¹).integral_comp
      ((Homeomorph.mulRight b⁻¹).measurableEmbedding) (S.penaltyWeight β)
    rw [integral_const_mul, h, ← penaltyZ, inv_mul_cancel₀ (S.penaltyZ_pos β).ne']
  unfold noise prior
  rw [integral_fintype_prod_eq_prod (fun (b : Edge (Site c)) u => (S.penaltyZ β G)⁻¹ *
    S.penaltyWeight β (u * (Q b)⁻¹))]
  simp_rw [he]; simp

/-- The actual branch kernel property. -/
structure IsKernel (β : ℝ) (G : Gauge) : Prop where
  positive (U : Config G f) V : 0 ≤ S.density β U V
  meas : Measurable fun x : Config G f × Config G c => S.density β x.1 x.2
  bound : ∃ C : ℝ, ∀ U : Config G f, ∀ V, S.density β U V ≤ C
  integrable (U : Config G f) : Integrable (S.density β U) (prior G c)
  total (U : Config G f) : (∫ V : Config G c, S.density β U V ∂prior G c) = 1

theorem density_positive (β : ℝ) (U : Config G f) (V : Config G c) : 0 ≤ S.density β U V := by
  refine Finset.sum_nonneg fun t _ ↦ mul_nonneg (S.likelihood_pos U t) ?_
  apply Finset.prod_nonneg
  intro b _; exact mul_nonneg (inv_pos.2 (S.penaltyZ_pos _)).le (Real.exp_pos _).le

theorem density_meas (h : S.patch.Branches S.kernel G) (β : ℝ) : Measurable fun x : Config G f × Config G c => S.density β x.1 x.2 := by
  unfold density; refine Finset.measurable_fun_sum _ fun t _ ↦ ?_
  have hu : Measurable fun x : Config G f × Config G c => S.prediction x.1 t :=
    (S.prediction_meas h t).comp measurable_fst
  have hw : Measurable fun x : Config G f × Config G c => (S.prediction x.1 t,x.2) :=
    hu.prodMk measurable_snd
  have hn : Measurable fun x : Config G f × Config G c => S.noise β (S.prediction x.1 t) x.2 := by
    change Measurable ((fun x : Config G c × Config G c => S.noise β x.1 x.2) ∘
      fun x : Config G f × Config G c => (S.prediction x.1 t,x.2))
    exact (S.noise_cont (G := G) β).measurable.comp hw
  have hl : Measurable fun x : Config G f × Config G c => S.likelihood x.1 t :=
    (S.likelihood_meas h t).comp measurable_fst
  exact hl.mul hn

theorem density_bound (h : S.patch.Branches S.kernel G) (β : ℝ) : ∃ C : ℝ, ∀ U : Config G f, ∀ V, S.density β U V ≤ C := by
  obtain ⟨A, HA⟩ := (isCompact_range (S.noise_cont (G := G) β)).bddAbove
  refine ⟨A, fun U V ↦ ?_⟩
  calc
    _ ≤ ∑ t, S.likelihood U t * A := Finset.sum_le_sum fun t _ ↦
      mul_le_mul_of_nonneg_left (HA ⟨(S.prediction U t,V),rfl⟩) (S.likelihood_pos U t)
    _ = _ := by rw [← Finset.sum_mul, S.chosen h, one_mul]

theorem density_integrable (β : ℝ) (U : Config G f) : Integrable (S.density β U) (prior G c) := by
  unfold density
  apply integrable_finsetSum; intro i _
  exact (S.noise_integrable β (S.prediction U i)).const_mul _

theorem density_total (h : S.patch.Branches S.kernel G) (β : ℝ) (U : Config G f) : (∫ V : Config G c, S.density β U V ∂prior G c) = 1 := by
  unfold density
  rw [integral_finsetSum _]
  · simp_rw [integral_const_mul, S.noise_mass, mul_one]; exact S.chosen h U
  intro i _; exact (S.noise_integrable β _).const_mul _

theorem isKernel (h : S.patch.Branches S.kernel G) (β : ℝ) : S.IsKernel β G :=
  { positive := S.density_positive β
    meas := S.density_meas h β
    bound := S.density_bound h β
    integrable := S.density_integrable β
    total := S.density_total h β }
end StepData
end YM.RG
