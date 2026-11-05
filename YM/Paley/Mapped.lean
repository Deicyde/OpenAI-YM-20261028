import YM.Distribution.Tests
import YM.Hilbert.Kolmogorov
import YM.Paley.Line


/-! Continuous-space Laplace test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Paley
open Function Set Filter MeasureTheory Measure Complex Analysis Boundary Probe
open scoped Topology NNReal ENNReal InnerProductSpace ContDiff
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] (x : X → ℝ) (hx : Continuous x) (hp : ∀ᵐ i ∂μ, 0 ≤ x i) (v : X→ℂ) (hv : Continuous v) (he : ∀ i, ‖v i‖=1)

def weight (z : ℂ) (t : X) := v t*Complex.exp ((x t:ℂ)*z*I)
def cell (z : ℂ) := ∫ p, weight x v z p ∂μ
include hp he
omit [TopologicalSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma column (s : ℂ) (hs : s∈high) : ∀ᵐ t ∂μ, ‖weight x v s t‖ ≤ 1 := by
  filter_upwards [hp] with i hi
  simp only [weight,norm_mul,he, one_mul,Complex.norm_exp]
  simp [mul_im,mul_re]; exact mul_nonneg hi hs

include hx hv
lemma ok (s : ℂ) (hs : s∈high) : Integrable (weight x v s) μ := by
  apply (integrable_const (μ := μ) (1:ℝ)).mono (by unfold weight;fun_prop)
  simpa using column μ x hp v he s hs
lemma heat : Air (cell μ x v) (μ.real univ) where
  connects := by
    refine continuousOn_of_dominated (F := weight x v) (bound := fun _ => 1)
      (fun i hi => (ok μ x hx hp v hv he i hi).aestronglyMeasurable)
      (fun i hi => column μ x hp v he i hi) (integrable_const _) (ae_of_all _ fun i => ?_)
    unfold weight; fun_prop
  bounded z hz := by
    unfold cell; apply (norm_integral_le_integral_norm _).trans
    simpa using (integral_mono_ae (ok μ x hx hp v hv he _ hz |>.norm)
      (integrable_const (1:ℝ)) (column μ x hp v he z hz))
  straight z hz := by
    let y := z.im/2
    have heZ : 0<z.im := hz
    have hy : 0<y := by unfold y; positivity
    have ht := ok μ x hx hp v hv he z (subset hz)
    let B := {p : ℂ| y<p.im}
    let g p i := (x i:ℂ)*I*weight x v p i
    have hh i p : HasDerivAt (fun z => weight x v z i) (g p i) p := by
      convert ((((hasDerivAt_id' p).const_mul ((x i):ℂ)).mul_const I).cexp.const_mul (v i)) using 1 <;> try rfl
      dsimp only [g,weight];ring
    have hw := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := weight x v) (F' := g) (μ := μ)
      (show B∈𝓝 z from (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (show y<z.im by dsimp only [y]; linarith))
      (Eventually.of_forall fun i => by unfold weight;fun_prop) ht (show AEStronglyMeasurable (g z) μ by unfold g weight;fun_prop) (bound := fun _ => y⁻¹)
    refine (hw ?_ (integrable_const _) (ae_of_all _ fun i p _ => hh i p)).2.differentiableAt.differentiableWithinAt
    filter_upwards [hp] with i hi p H
    dsimp only [g]; simp only [weight, norm_mul, he, norm_I, norm_real, Real.norm_eq_abs,abs_of_nonneg hi,mul_one,one_mul,Complex.norm_exp]
    rw [show (((x i : ℂ) * p)*I).re= -(x i*p.im) by simp]
    have hx := Real.add_one_le_exp (x i*p.im)
    rw [Real.exp_neg, inv_eq_one_div y, le_div_iff₀ hy, mul_right_comm,← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    nlinarith [show y<p.im from H]
end YM.Paley
