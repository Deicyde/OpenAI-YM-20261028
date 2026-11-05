import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Station
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04


set_option warningAsError false
/-!
# Opposite-momentum test conversion

The mixed derivative queried by the loop prescription is analytic
polarization in **two** external real fields, extended COMPLEX BILINEARLY
when stating a symbol formula. . Not complex value of a periodic
interpolant. Use arbitrary real-wave pairs in `Precision.wave`, including
harmonic and Nyquist cases (no divisions by momentum). Beware that their
amplitude bounds in the invoice are per color component. Here we can pay
it even from only an opposite *basis wave* test at the appropriate smaller
price, IF translation invariance. Its realization on actual determinants is
in `Translate`; no need to add a momentum-diagonal hypothesis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.QuantumRates.Waves
open Function Filter Lattice Wilson RG Precision Exterior Tree Bloch Matrix 
open  Bid 
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius ComplexConjugate

variable {G : Gauge} {c : Side}

abbrev Field (G : Gauge) (c : Side) := Body 1 c → G.ColorIndex → ℂ




def re (x : Field G c) : Dir G c := fun i => WithLp.toLp 2 fun j => (x i j).re
def im (x : Field G c) : Dir G c := fun i => WithLp.toLp 2 fun j => (x i j).im

def ext (F : Dir G c → Dir G c → ℝ) (x y : Field G c) :=
  Complex.ofReal (F (re x) (re y) - F (im x) (im y)) +
    Complex.I * Complex.ofReal (F (re x) (im y) + F (im x) (re y))

private lemma re_smul (z : ℂ) (x : Field G c) : re (z • x) = z.re • re x - z.im • im x := by
  funext i; ext j
  exact Complex.mul_re ..
private lemma im_smul (z : ℂ) (x : Field G c) : im (z • x) = z.re • im x + z.im • re x := by
  funext i; ext j
  exact Complex.mul_im ..

/-- Bundled complexification of real Hessians. -/
def liftB (D : Dir G c →ₗ[ℝ] Dir G c →ₗ[ℝ] ℝ) :
    Field G c →ₗ[ℂ] Field G c →ₗ[ℂ] ℂ where
  toFun x := {
    toFun y := Waves.ext (fun u v => D u v) x y
    map_add' y z := by
      unfold ext; rw [show re (y+z)=re y+re z from rfl,show im (y+z)=im y+im z from rfl]
      simp; ring
    map_smul' z y := by
      unfold ext; rw [re_smul,im_smul]; apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring }
  map_add' x y := by
    apply LinearMap.ext; intro z
    change Waves.ext (fun u v => D u v) (x+y) z = Waves.ext (fun u v => D u v) x z + Waves.ext (fun u v => D u v) y z
    unfold ext; rw [show re (x+y)=re x+re y from rfl,show im (x+y)=im x+im y from rfl]; simp; ring
  map_smul' z x := by
    apply LinearMap.ext; intro y
    change Waves.ext (fun u v => D u v) (z • x) y = z * Waves.ext (fun u v => D u v) x y
    unfold ext; rw [re_smul, im_smul]; apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
















end YM.Further.QuantumRates.Waves
