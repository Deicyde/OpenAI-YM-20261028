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
import YM.Work.A05.Read
import YM.Work.A07

/-!
# Ordered polarization of a square with quadratic argument
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Matrix Filter Function Set
open scoped Topology ContDiff BigOperators
variable {E F H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup H] [NormedSpace ℂ H]






structure Square (E F : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] where
  one : E →L[ℂ] F
  two : E →L[ℂ] E →L[ℂ] F
  Q : F →L[ℂ] F →L[ℂ] ℂ
  symm x y : Q x y = Q y x
namespace Square
variable (S : Square E F)

def arg (x : E) := S.one x + S.two x x

def cross (x y : E) := S.two x y + S.two y x

def term (x y : E) := S.one y + S.cross x y





@[simp] lemma arg_zero : S.arg 0 = 0 := by simp [arg]
@[simp] lemma term_zero (y : E) : S.term 0 y = S.one y := by simp [term,cross]










end Square
end YM.Push.Loops.Paths
