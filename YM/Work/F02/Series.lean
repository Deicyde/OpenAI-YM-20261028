import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Liouville
import YM.Analysis.Polydisc



/-!
# Normal convergence lemma for the path expansions

Several complex variables; we get summable bounds also for the Frechet derivative on a
smaller ball by the one-variable Cauchy estimate. So we can use `YM.PolyDisc.finiteD`.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.F02

open Filter Metric
open scoped Topology

variable {ι X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- A dimension-independent first derivative bound on the open half ball. Used for
series of polynomials (we assume each individual function is already complex differentiable,
so estimating on all lines suffices for the bound). -/
lemma fderiv_bound {f : X → Y} {x y : X} {B R : ℝ}
    (hf : Differentiable ℂ f)
    (hR : 0 < R)
    (h : ∀ z ∈ ball x R, ‖f z‖ ≤ B)
    (hy : y ∈ ball x (R / 2)) :
    ‖fderiv ℂ f y‖ ≤ B / (R / 2) := by
  have hr : 0 < R / 2 := half_pos hR
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (h x (mem_ball_self hR))
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hB hr.le)
  intro v hv
  let g : ℂ → X := fun t => y + t • v
  have hg : Differentiable ℂ g :=
    (differentiable_const _).add (differentiable_id.smul_const v)
  have hd : HasDerivAt g v 0 := by
    simpa [g] using! (((hasDerivAt_id' (0 : ℂ)).smul_const v).const_add y)
  have he : g 0 = y := by simp [g]
  have hc := (hf (g 0)).hasFDerivAt.comp_hasDerivAt 0 hd
  rw [he] at hc
  rw [← hc.deriv]
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    ((hf.comp hg).diffContOnCl) ?_
  intro t ht
  apply h (g t)
  have hp : dist (g t) y = R / 2 := by
    simpa [g, dist_eq_norm, norm_smul, hv, Metric.mem_sphere] using ht
  rw [mem_ball] at hy ⊢
  linarith [dist_triangle (g t) y x]

/-- Summably dominated series of entire functions, analytic at the center. -/
lemma analytic_series [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
    (f : ι → X → Y) {x : X} {R : ℝ} {u : ι → ℝ} (hR : 0 < R)
    (hf : ∀ i, Differentiable ℂ (f i)) (hu : Summable u)
    (h : ∀ i z, z ∈ ball x R → ‖f i z‖ ≤ u i) :
    AnalyticAt ℂ (fun z => ∑' i, f i z) x := by
  letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ ℂ X
  haveI := FiniteDimensional.complete ℂ Y
  have hr : 0 < R / 2 := half_pos hR
  have hu' : Summable (fun i => u i / (R / 2)) := by
    simpa only [div_eq_mul_inv] using hu.mul_right (R / 2)⁻¹
  apply PolyDisc.finiteD
  filter_upwards [ball_mem_nhds x hr] with y hy
  exact (hasFDerivAt_tsum_of_isPreconnected hu' isOpen_ball
    (convex_ball x _).isPreconnected
    (fun i z _ => ((hf i) z).hasFDerivAt)
    (fun i _ => fderiv_bound (hf i) hR (h i))
    (mem_ball_self hr)
    (.of_norm_bounded hu (fun i => h i x (mem_ball_self hR))) hy).differentiableAt

end YM.Work.F02
