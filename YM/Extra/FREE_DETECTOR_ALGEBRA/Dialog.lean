import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Extra.FREE_DETECTOR_ALGEBRA.Frobenius
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06

set_option warningAsError false

/-!
# Scalar color combinations and equivariant section of shell constraints

Finite Real color space throughout. Using projected orthogonal-adjoint
representation with physical metric; equation projection is NOT dropping a
formal color coordinate or independent change of reference basis per use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {F M : Type*} [NormedAddCommGroup F] [NormedAddCommGroup M] {j : ℕ}

section color
variable [NormedSpace ℝ F] [NormedSpace ℝ M]

def dye (L : F→L[ℝ] M) : TwoJet F j →ₗ[ℝ] TwoJet M j where
  toFun Q := fun a b => L.compContinuousMultilinearMap (Q a b)
  map_add' := by intro p q; ext1 a; ext1 b; ext1 v; exact map_add L _ _
  map_smul' := by intro t p; ext1 a; ext1 b; ext1 v; exact map_smul L _ _

lemma dye_sol (p : Sol F j) (L : F→L[ℝ] M) : dye L p.val ∈ onShell M j := by
  have he := composeColor L p.wave
  constructor
  · constructor
    · intro i m v σ; exact congr_arg L (p.closed.coeffSym i m v σ)
    · intro i m; ext1 v
      change L (p.val i m v) = -L (p.val m i v)
      nth_rw 1 [p.closed.antisymmetric i m]; exact map_neg L _
    intro i m a x; exact he.cycle i m a x (mem_univ _)
  intro i x; exact he.divergence i x (mem_univ _)

def insertColor (L : F→L[ℝ] M) (j : ℕ) : Sol F j →ₗ[ℝ] Sol M j :=
  ((dye L).comp (onShell F j).subtype).codRestrict _ (fun q => dye_sol q L)


end color



variable {G : Gauge}

def conjG (u : G.El) : G.Color →L[ℝ] G.Color := (G.adjoint u).toContinuousLinearMap



def actionG (u : G.El) (j : ℕ) : Sol G.Color j →ₗ[ℝ] Sol G.Color j := insertColor (conjG u) j



@[simp] theorem oneSol (p : Sol G.Color j) : actionG (1:G.El) j p=p := by
  apply Subtype.ext; ext1 i; ext1 m; ext1 w; exact G.adjoint_one (p.val i m w)









/-- First curl radial arbitrary Taylor, then project on Maxwell shell (not
claiming that simply eliminating the off-shell equations from G-invariants
*as an ideal of the invariant ring* gives this section). -/
def sendTo (G : Gauge) (j : ℕ) : Taylor G j →ₗ[ℝ] Sol G.Color j := asSol.comp ((formSpace _ G.Color).subtype.comp potential.toLinearMap)





theorem sends_back (P : Sol G.Color j) : sendTo G j (gaugeJet P)=P := by change asSol (takeCurl _)=_; rw [match_leg,asSol_self]
end YM.Extra.FD
