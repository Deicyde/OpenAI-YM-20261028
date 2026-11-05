import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flux
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Hot

/-!
# From the exponential moment estimate to absolute moment and tail certificates

To simplify reuse (even at full physical reads) we allow the normalized
location Y whose law is controlled to be a measurable function. Integrals
are always under the SAME given measure. `Costed` pays L¹ and tail bills for
actual measurable probes, not formal moments. Its `value_tail` / `uniform`
use the ordinary tail criterion for uniform integrability (can use even as
the measures and types vary). For sets in the tail proof still need the
set measurability theorem -- no assumption for a rebranched read on some
new geometry. This file does not assert support rents.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C
open Function Filter Set Matrix MeasureTheory
open Next.SectorChange.Gaussian
open AnalyticBridge.LocalGaussianLaws
open SectorTools
open scoped Topology BigOperators

variable {I : Type} [Fintype I]
variable {K : ℕ} {E M : ℝ}

def reserve (K : ℕ) (E : ℝ) := heat K E / 2
lemma reserve_pos (K : ℕ) (hE : 0 ≤ E) : 0 < reserve K E := half_pos (heat_pos K hE)

lemma fuel_reserve_le (hE : 0 ≤ E) (z : Vec I) : fuel (reserve K E) z ≤ fuel (heat K E) z :=
  Real.exp_monotone (mul_le_mul_of_nonneg_right (half_le_self (heat_pos K hE).le) (energy_nonneg z))
lemma fuel_reserve_sq (z : Vec I) : fuel (reserve K E) z ^ 2 = fuel (heat K E) z := by
  unfold fuel reserve; rw [sq, ← Real.exp_add]; ring_nf
lemma fuel_reserve_tail (hE : 0 ≤ E) (z : Vec I) (R : ℝ) (hR : 0 ≤ R) (hr : R ≤ countingNorm z) :
    fuel (reserve K E) z ≤ Real.exp (-reserve K E*R^2) * fuel (heat K E) z := by
  have hs := pow_le_pow_left₀ hR hr 2; rw [countingNorm_squared] at hs
  unfold fuel; rw [← Real.exp_add]; apply Real.exp_monotone
  have hb := mul_le_mul_of_nonneg_left hs (heat_pos K hE).le
  unfold reserve; linarith only [hb]

variable {X α : Type*} [NormedAddCommGroup X] [MeasurableSpace X] [MeasurableSpace α]

/-- Pointwise price in the earned exponential currency. -/
structure Moderate (K : ℕ) (E M : ℝ) (f : Vec I → X) : Prop where
  nonneg : 0 ≤ M
  borel : Measurable f
  hold (z) : ‖f z‖ ≤ M*fuel (reserve K E) z

/-- Absolute estimates with their integrability proofs. Here Y is the
normalized local read (use `id` on the two normalized measures). -/
structure Costed (K : ℕ) (E M : ℝ) (μ : Measure α) (Y : α → Vec I) (f : α → X) : Prop where
  nonneg : 0 ≤ M
  borel : Measurable f
  reader : Measurable Y
  first : Integrable f μ
  first_bound : (∫ z, ‖f z‖ ∂μ) ≤ M * kiln K E
  second : Integrable (fun z => ‖f z‖^2) μ
  second_bound : (∫ z, ‖f z‖^2 ∂μ) ≤ M^2 * kiln K E
  /-- Tail at the read locations, even within any specified set. -/
  tail (R : ℝ) (hR : 0 ≤ R) (s : Set α) (hs : MeasurableSet s) (ht : ∀ z ∈ s, R ≤ countingNorm (Y z)) :
    (∫ z in s, ‖f z‖ ∂μ) ≤ M * kiln K E * Real.exp (-reserve K E*R^2)

variable [OpensMeasurableSpace X]

section construct
variable [SecondCountableTopology X] {f : Vec I → X} {μ : Measure α} {Y : α → Vec I}

lemma cost_at (hf : Moderate K E M f) (hE : 0 ≤ E) (hy : Measurable Y)
    (hp : Integrable (fuel (heat K E) ∘ Y) μ) (hc : (∫ z, fuel (heat K E) (Y z) ∂μ) ≤ kiln K E) :
    Costed K E M μ Y (f ∘ Y) := by
  let F := f ∘ Y
  let g z := fuel (heat K E) (Y z)
  have hi : Integrable g μ := hp
  have hm := hf.nonneg
  have hF : Measurable F := hf.borel.comp hy
  have h1 (z : α) : ‖F z‖ ≤ M*g z :=
    (hf.hold _).trans (mul_le_mul_of_nonneg_left (fuel_reserve_le hE _) hm)
  have hI : Integrable F μ := (hi.const_mul M).mono' hF.aestronglyMeasurable (Eventually.of_forall h1)
  have h2 (z : α) : ‖F z‖ ^ 2 ≤ M^2*g z := by
    have hh := pow_le_pow_left₀ (norm_nonneg (F z)) (hf.hold (Y z)) 2
    rwa [mul_pow, fuel_reserve_sq] at hh
  have hJ : Integrable (fun z => ‖F z‖^2) μ := (hi.const_mul _).mono' (hF.norm.pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun z => (Real.norm_of_nonneg (sq_nonneg _)).trans_le (h2 z))
  refine ⟨hm,hF,hy,hI,?_,hJ,?_,?_⟩
  · refine (integral_mono hI.norm (hi.const_mul _) h1).trans ?_; rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hc hm
  · refine (integral_mono hJ (hi.const_mul _) h2).trans ?_; rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hc (sq_nonneg _)
  intro R hR s hs ht
  let t := Real.exp (-reserve K E*R^2)
  have hh : 0 ≤ M*t := mul_nonneg hm (Real.exp_pos _).le
  have he : (fun z => ‖F z‖) ≤ᵐ[μ.restrict s] fun z => (M*t)*g z := by
    filter_upwards [ae_restrict_mem hs] with z hz
    rw [mul_assoc]; exact (hf.hold (Y z)).trans
      (mul_le_mul_of_nonneg_left (fuel_reserve_tail hE _ R hR (ht z hz)) hm)
  refine (integral_mono_ae hI.norm.integrableOn (hi.const_mul (M*t)).integrableOn he).trans ?_
  rw [integral_const_mul]
  change M*t*(∫ z in s, g z ∂μ) ≤ M * kiln K E * t
  rw [mul_right_comm M (kiln K E)]; refine mul_le_mul_of_nonneg_left ?_ hh
  exact (setIntegral_le_integral hi (Eventually.of_forall fun z => (fuel_pos _ _).le)).trans hc

variable {ν : Measure (Vec I)}



theorem Hot.costed (h : Hot K E ν) (hE : 0 ≤ E) (hf : Moderate K E M f) :
    Costed K E M ν id f := cost_at hf hE measurable_id h.paid h.cap
end construct

section tails
variable {f : α → X} {μ : Measure α} {Y : α → Vec I}

omit [OpensMeasurableSpace X] in
lemma Costed.counting_tail (h : Costed K E M μ Y f) (R : ℝ) (hR : 0 ≤ R) :
    (∫ z in {z | R ≤ countingNorm (Y z)}, ‖f z‖ ∂μ) ≤ M * kiln K E * Real.exp (-reserve K E*R^2) := by
  refine h.tail R hR _ (measurableSet_le measurable_const ?_) fun z hz => hz
  exact continuous_countingNorm.measurable.comp h.reader

omit [OpensMeasurableSpace X] in
lemma Costed.norm_tail (h : Costed K E M μ Y f) (R : ℝ) (hR : 0 ≤ R) :
    (∫ z in {z | R ≤ ‖Y z‖}, ‖f z‖ ∂μ) ≤ M * kiln K E * Real.exp (-reserve K E*R^2) := by
  refine h.tail R hR _ (measurableSet_le measurable_const h.reader.norm) ?_
  exact fun z hz => (show R ≤ ‖Y z‖ from hz).trans (norm_le_countingNorm _)

/-- Tail in the uniform integrability criterion (measure allowed to vary). -/
theorem Costed.value_tail (h : Costed K E M μ Y f) (T : ℝ) (hT : 0 < T) :
    (∫ z in {z | T ≤ ‖f z‖}, ‖f z‖ ∂μ) ≤ M^2 * kiln K E / T := by
  let s := {z | T ≤ ‖f z‖}
  have hi : (fun z => T * ‖f z‖) ≤ᵐ[μ.restrict s] fun z => ‖f z‖^2 := by
    filter_upwards [ae_restrict_mem (μ:=μ) (measurableSet_le measurable_const h.borel.norm)] with z hz
    rw [sq]; exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  apply (le_div_iff₀ hT).mpr
  rw [mul_comm _ T, ← integral_const_mul]
  exact (integral_mono_ae (h.first.norm.const_mul T).integrableOn h.second.integrableOn hi).trans
    ((setIntegral_le_integral h.second (Eventually.of_forall fun z => sq_nonneg _)).trans h.second_bound)

variable [IsFiniteMeasure μ]

omit [OpensMeasurableSpace X] in
lemma Costed.small_set (h : Costed K E M μ Y f) (T : ℝ) (hT : 0 < T) (s : Set α) :
    (∫ z in s, ‖f z‖ ∂μ) ≤ T*μ.real s + M^2*kiln K E / T := by
  let A := fun z => T⁻¹*‖f z‖^2
  have hi : ∀ z, ‖f z‖ ≤ T + A z := fun z => by
    unfold A; rw [inv_mul_eq_div]; have hx := sq_nonneg (‖f z‖ - T)
    rw [← sub_le_iff_le_add']; apply (le_div_iff₀ hT).mpr
    nlinarith only [hx, sq_nonneg T, mul_nonneg (norm_nonneg (f z)) hT.le, sq_nonneg ‖f z‖]
  have hh : Integrable A μ := h.second.const_mul _
  refine (integral_mono h.first.norm.integrableOn ((integrable_const T).add hh.integrableOn) hi).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const T) hh.integrableOn, setIntegral_const, smul_eq_mul, mul_comm T]
  refine add_le_add_right ((setIntegral_le_integral hh (Eventually.of_forall fun z => ?_)).trans ?_) _
  · exact mul_nonneg (inv_pos.mpr hT).le (sq_nonneg _)
  unfold A; rw [integral_const_mul, inv_mul_eq_div]; exact div_le_div_of_nonneg_right h.second_bound hT.le

/-- A threshold on the probe values; depends only on a committed price
bound `W` (for all probes in question) and ε along with K, E. -/
def valueLevel (K : ℕ) (E W ε : ℝ) : ℝ := 1 + 2*(W^2*kiln K E)/ε
lemma valueLevel_pos (K : ℕ) (E W : ℝ) {ε : ℝ} (he : 0 < ε) : 0 < valueLevel K E W ε := by
  unfold valueLevel; have := kiln_pos K E; positivity

/-- Along with the absolute L¹ estimate in the certificate, the standard
uniform integrability bills once M has a common bound W. -/
theorem Costed.uniform (h : Costed K E M μ Y f) {W ε : ℝ} (hh : M ≤ W) (he : 0 < ε) :
    let t := valueLevel K E W ε
    (∀ u, t ≤ u → (∫ z in {z | u ≤ ‖f z‖}, ‖f z‖ ∂μ) ≤ ε/2) ∧
    0 < ε/(2*t) ∧
    ∀ s : Set α, μ.real s ≤ ε/(2*t) → (∫ z in s, ‖f z‖ ∂μ) ≤ ε := by
  intro t
  have ht : 0 < t := valueLevel_pos K E W he
  have hx := kiln_pos K E
  have hu {u : ℝ} (hb : t ≤ u) : M^2*kiln K E / u ≤ ε/2 := by
    have hh' : (t-1)*ε = 2*(W^2*kiln K E) := by
      unfold t valueLevel; field_simp; ring
    apply (div_le_iff₀ (ht.trans_le hb)).mpr
    nlinarith only [hh', he, mul_le_mul_of_nonneg_right hb he.le,
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h.nonneg hh 2) hx.le]
  refine ⟨fun u h' => (h.value_tail u (ht.trans_le h')).trans (hu h'), by positivity, fun s hs => ?_⟩
  have hq := (le_div_iff₀ (show 0 < 2*t by positivity)).mp hs
  exact (h.small_set t ht s).trans (by linarith only [hq,hu (show t ≤ t from le_rfl)])

end tails
end YM.PhysicalNext.WeightedGaussianMarginal45C
