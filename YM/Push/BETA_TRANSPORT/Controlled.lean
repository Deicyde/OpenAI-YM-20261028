import YM.Push.BETA_TRANSPORT.Block

/-! Iterating the real chain rule with Bochner insertions. The bounds have common
neighborhoods in β (pointwise bounds in the configuration, integrable majorants).
Used in multi-step applications in `History`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG Gibbs MeasureTheory Filter Set
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {c f : Side} {G : Gauge}
structure Parameter (b r : ℝ → ℝ) : Prop where
  has z : HasDerivAt b (r z) z
  bound x : ∃ D : ℝ, ∀ᶠ z in 𝓝 x, |r z| ≤ D
namespace Parameter
variable {b r : ℝ → ℝ}
lemma both (h : Parameter b r) (x : ℝ) : ∃ D R : ℝ, 0 ≤ D ∧ 0 ≤ R ∧ ∀ᶠ z in 𝓝 x, |r z| ≤ D ∧ |b z| ≤ R := by
  obtain ⟨D,hD⟩ := h.bound x
  exact ⟨max D 0,|b x|+1,le_max_right ..,by positivity,(hD.and ((h.has x).continuousAt (eventually_abs_bound _))).mono
      fun z hz => ⟨hz.1.trans (le_max_left ..),hz.2⟩⟩
lemma line (a b : ℝ) : Parameter (fun z => z*a+b) (fun _ => a) :=
  ⟨fun z => by simpa using ((hasDerivAt_id' z).mul_const a).add_const b,
    fun _ => ⟨_,Eventually.of_forall fun _ => le_refl _⟩⟩
end Parameter

variable {X α : Type*} [MeasurableSpace α] [NormedAddCommGroup X] [NormedSpace ℝ X]

structure Controlled (μ : Measure α) (F F' : ℝ → α → X) : Prop where
  int z : Integrable (F z) μ ∧ Integrable (F' z) μ
  has z U : HasDerivAt (F · U) (F' z U) z
  cost x : ∃ M N : α → ℝ, Integrable M μ ∧ Integrable N μ ∧ ∀ᶠ z in 𝓝 x, ∀ U, ‖F z U‖ ≤ M U ∧ ‖F' z U‖ ≤ N U

namespace Controlled
variable {b r : ℝ → ℝ} {μ : Measure α} {F F' : ℝ → α → X}
lemma const {F : α → X} (hf : Integrable F μ) : Controlled μ (fun _ => F) (fun _ _ => 0) :=
  ⟨fun _ => ⟨hf,integrable_zero _ _ _⟩,fun z _ => hasDerivAt_const z _,fun _ => ⟨_,_,hf.norm, (integrable_zero _ _ _),
    Eventually.of_forall fun _ _ => ⟨le_rfl, norm_zero.le⟩⟩⟩
lemma weight (h : Controlled μ F F') {w w' : ℝ → α → ℝ} {A C} (hw : WeightEstimate w w' A C) (hb : Parameter b r) :
    Controlled μ (fun z x => w (b z) x • F z x) (fun z x => w (b z) x • F' z x + r z • w' (b z) x • F z x) := by
  refine ⟨fun z => ⟨hw.smul_integrable _ (h.int z).1,(hw.smul_integrable _ (h.int z).2).add
    ((hw.slope_integrable (b z) (h.int z).1).smul (r z))⟩,fun z x => ?_,fun x => ?_⟩
  · rw [smul_smul]; exact ((hw.has _ x).scomp z (hb.has z)).smul (h.has z x)
  obtain ⟨D,R,hD,hR,hr⟩ := hb.both x; obtain ⟨M,N,hM,hN,he⟩ := h.cost x
  refine ⟨_,_,hM.const_mul (C R), (hN.const_mul (C R)).add (hM.const_mul (D*(A*C R))), ?_⟩
  filter_upwards [hr,he] with z ⟨hr,hb⟩ hz U
  have h0 := hw.capWeight R hR
  have hv : ‖w (b z) U‖ ≤ C R := (Real.norm_of_nonneg (hw.nonneg ..)).trans_le (hw.le hb _)
  have hu := (hw.slope _ U).trans (mul_le_mul_of_nonneg_left (hw.le hb _) hw.cap)
  constructor
  · rw [norm_smul]; exact mul_le_mul hv (hz U).1 (norm_nonneg _) h0
  apply (norm_add_le ..).trans
  rw [norm_smul,norm_smul,norm_smul,← mul_assoc]
  exact add_le_add (mul_le_mul hv (hz U).2 (norm_nonneg _) h0) (mul_le_mul
    (mul_le_mul hr hu (norm_nonneg _) hD) (hz U).1 (norm_nonneg _) (mul_nonneg hD (mul_nonneg hw.cap h0)))

variable [CompleteSpace X]
set_option linter.unusedSectionVars false in
lemma derivative (h : Controlled μ F F') (x : ℝ) : HasDerivAt (fun z => ∫ U, F z U ∂μ) (∫ U, F' x U ∂μ) x := by
  obtain ⟨_,_,_,hN,he⟩ := h.cost x
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le he
    (Eventually.of_forall fun z => (h.int z).1.1) (h.int x).1 (h.int x).2.1 (Eventually.of_forall fun U z hz => (hz U).2)
    hN (Eventually.of_forall fun U z _ => h.has z U)).2

lemma pushed {F F' : ℝ → Config G f → X} {S : StepData c f} (hS : S.patch.Branches S.kernel G) (hb : Parameter b r)
    (h : Controlled (prior G f) F F') : Controlled (prior G c) (fun z => S.push (b z) (F z))
      (fun z => S.push (b z) (F' z) + r z • pushSlope S (b z) (F z)) := by
  refine ⟨fun z => ⟨StepData.push_integrable (S.isKernel hS _) _ (h.int z).1,(StepData.push_integrable
    (S.isKernel hS _) _ (h.int z).2).add ((pushSlope_integrable S hS (h.int z).1 _).smul (r z))⟩,fun z V => ?_, fun x => ?_⟩
  · have he := slice_estimate S hS V
    simp only [Pi.add_apply,StepData.push,Pi.smul_apply,pushSlope,← integral_smul]
    rw [← integral_add (he.smul_integrable _ (h.int _).2) (f:=fun x => S.density (b z) x V • F' z x)
      (g:=fun x => r z • densitySlope S (b z) x V • F z x) ((he.slope_integrable _ (h.int _).1).smul _)]
    exact (h.weight he hb).derivative z
  obtain ⟨D,R,hD,hR,hr⟩ := hb.both x; obtain ⟨M,N,hM,hN,he⟩ := h.cost x
  let C := noiseCost S R; let A := noiseCap S
  let paid (M : Config G f → ℝ) : ℝ := C* ∫ U, M U ∂prior G f
  refine ⟨fun _ => paid M,fun _ => paid N + D*(A*paid M),integrable_const _,integrable_const _,?_⟩
  filter_upwards [he,hr] with z hz ⟨hd,hb⟩ V
  have hh := slice_estimate S hS V
  have ht {E : Config G f → X} (hE : Integrable E (prior G f)) (N : Config G f → ℝ) (hN : Integrable N (prior G f))
      (hn : ∀ U, ‖E U‖ ≤ N U) : S.push (b z) (fun U => ‖E U‖) V ≤ paid N := by
    unfold paid; rw [← integral_const_mul]; exact integral_mono (hh.smul_integrable _ hE.norm) (hN.const_mul _) fun x =>
      mul_le_mul (hh.le hb x) (hn x) (norm_nonneg _) (hh.capWeight _ hR)
  refine ⟨(hh.norm_integral_le _ (h.int z).1).trans (ht (h.int z).1 M hM fun U => (hz U).1), (norm_add_le ..).trans ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact add_le_add ((hh.norm_integral_le _ (h.int z).2).trans (ht (h.int z).2 N hN fun U => (hz U).2))
    (mul_le_mul hd ((pushSlope_norm_le _ hS (h.int z).1 ..).trans (mul_le_mul_of_nonneg_left (ht (h.int z).1 M hM fun U =>
      (hz U).1) hh.cap)) (norm_nonneg _) hD)
end Controlled
end YM.Push.BetaTransport
