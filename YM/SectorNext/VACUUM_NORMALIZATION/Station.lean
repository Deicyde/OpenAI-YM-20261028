import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import YM.Pressure.Seeds




/-!
# Legitimate scalar log in the actual hessian germ

Consumes the PriceGap and analytic *tester* part of Critical; no oracle
postulating determinant sign.

Per real Haar-normalized color dimension
(no missing norm factor), works even for empty key set.

All the inputs
here about the flat germs / vectors, not the existence of stationary
kin/path.

Converse directions or trace routing at nonzero momentum not here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open RG Precision Function Matrix Lattice Tree Wilson Filter
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {c f : Side} {S : StepData c f} {G : Gauge} (F : Forest S.ratio) (t : S.Choices) (p : Clip) (R : PathData G)

def keys (x : Key F G → ℝ) := ∑ i : Key F G,x i • frame F i

lemma keys_at (x : Key F G → ℝ) (i : F.Free) : keys F x i = WithLp.toLp 2 (fun j : G.ColorIndex => x (i,j)) := by
  unfold keys frame
  rw [Finset.sum_apply,Fintype.sum_prod_type]
  have he (u : F.Free) (v : G.ColorIndex) : (x (u,v) • Pi.single u (EuclideanSpace.basisFun G.ColorIndex ℝ v) : AxisChart G F) i=
      if i=u then x (u,v) • EuclideanSpace.basisFun G.ColorIndex ℝ v else 0 := by
    by_cases h : i=u <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_eq_single i]
  · simp only [if_true]; apply PiLp.ext; intro j
    simp [EuclideanSpace.basisFun_apply,Pi.single_apply,mul_ite]
  · intro b _ hb; simp [Ne.symm hb]
  intro h; exact (h (Finset.mem_univ _)).elim














end YM.SectorNext.Vacuum
