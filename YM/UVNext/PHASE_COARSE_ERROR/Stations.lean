import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Next.UV_STRESS.Range


set_option warningAsError false

/-! # Feed both grill ports on the SAME order; stop-rate solution -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PhaseCoarse
open Function Filter Set MeasureTheory Analysis Extraction Lattice Wilson RG Overlay Marker Cells Next.UVStress Mix 
open scoped Topology BigOperators
variable {G : Gauge} (C : Family G) (f : Extraction.Order) {h k ℓ d : ℕ}

def overhead (h ℓ d : ℕ) := Real.exp (Stock.expPrice C h ℓ d 1 1 2 2 1) * (lenses C ℓ).order.factorial

/-- After all-copy root, explicit price per cell, **no dependences on
F.mesh/F.per, number of L steps etc except last wallet & fixed stop**.
Thus e.g. increasing radius by exp(τ*s_k) gives exp(-τ*s_k)
approximation, no per-step stop loss. -/
lemma pay (W : ℝ) (hW : 0 < W) :
    Real.exp (Stock.expPrice C h ℓ d (W/((lenses C ℓ).order.factorial:ℝ)) 1 2 2 1) = overhead C h ℓ d / W := by
  have ht : 0 < ((lenses C ℓ).order.factorial:ℝ) := by positivity
  rw [show Stock.expPrice C h ℓ d (W/((lenses C ℓ).order.factorial:ℝ)) _ _ _ _ = Stock.expPrice C h ℓ d 1 1 2 2 1 -
    Real.log (W/((lenses C ℓ).order.factorial:ℝ)) from ?_,Real.exp_sub,Real.exp_log (div_pos hW ht),overhead]; field_simp
  unfold Stock.expPrice; rw [Real.log_one,sub_zero]
















end YM.UVNext.PhaseCoarse
