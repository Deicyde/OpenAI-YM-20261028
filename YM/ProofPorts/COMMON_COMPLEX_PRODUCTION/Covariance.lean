import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import YM.MultiNext.VACUUM_STABILITY.Holding.Offers
import YM.Next.UV_STRESS.Annulus
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.PRICE_COMPILER.Suppression
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Schur


/-!
# Bounds on the law used by the sector integrals

Real, in counting coordinates. No claim about a V derivative through a flag.
Use the symmetrized window table of SectorChange itself (NOT a table
fitted to each perturbation of the scalar density, not the pre-L free
metric of Rack). Near an unforced component's good domain an extension
with quantitative jets will still be needed. Here buy zero-order spectral
and integration constants on every *actual* permitted output-seed table.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction
open Function Filter Finset Matrix Lattice RG Wilson Precision Multi.Vacuum Gauss
open Next.SectorChange Pressure Tree Gaussian Schur Wisps
open scoped Topology BigOperators Classical MatrixOrder

variable {I J β : Type} [Fintype I] [Fintype J]

def Ceiling (C : Matrix I I ℝ) (K : ℝ) := ∀ z : Vec I, z ⬝ᵥ (C *ᵥ z) ≤ K*sumSq z

lemma gram_cost (q : Matrix I J ℝ) (C : Matrix I I ℝ) (K : ℝ) (h : q*qᵀ = C) (hK : Ceiling C K) :
    Gauss.adjBound (I:=I) (J:=J) q K := by
  intro z
  have he : Gauss.mapRows (Function.swap q) z=qᵀ *ᵥ z := rfl
  rw [he]; change sumSq (qᵀ *ᵥ z) ≤ K*sumSq z
  rw [sumSq_dot,mulVec_transpose, ← dotProduct_mulVec, ← mulVec_transpose q, mulVec_mulVec,h]
  exact hK z

lemma root_gram [DecidableEq I] (C : Matrix I I ℝ) (h : C.PosDef) : CFC.sqrt C * (CFC.sqrt C)ᵀ=C := by
  have he : (CFC.sqrt C).IsSymm := Matrix.isHermitian_iff_isSymm.mp (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian
  rw [he]; exact CFC.sqrt_mul_sqrt_self C h.posSemidef.nonneg







/- Restricting the covariance (as opposed to the precision). No cost even
for a query at many sites, including overlap color blocks. Need an injection
or a separate norm for the projection. -/










variable {G : Gauge}
 


end YM.ProofPorts.CommonComplexProduction
