import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.PSeries
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Pre
import YM.Further.QUANTUM_RATES_PORT.Waves
import YM.Next.BOUNDARY.Coordinates
import YM.Next.SCHEDULE.Blocks
import YM.Work.A01.Conserve
import YM.Work.A03
import YM.Work.A04

set_option warningAsError false
/-!
# Optional momentum-side input form for the port (K' normalization)

What exactly to ask for if working with momentum/precision outputs.
No relying on the convention for high-alias or contour amplitudes;
just complexify real quadratic forms at the actual torus. Use `cell`
(initial-site convention) and `Row` with positive convolution sign.
This file is evaluation of the whole kinetic link precision from the
base Bed. Curvature output symbols treated separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.QuantumRates.Fiber
open Function Filter Lattice Wilson RG Precision Exterior Tree  Bid Bloch Finset Matrix
open Extra.Iteration  Waves
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {n : Side}






section row
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def train (p : Site n) (a : I → ℂ) : Co n I → ℂ := fun x => cell p x.1 * a x.2



omit [DecidableEq I] in
lemma per_site (p : Site n) (a b : I → ℂ) :
    dotProduct (train (-p) a) (train p b)=Fintype.card (Site n) * dotProduct a b := by
  unfold dotProduct; rw [Fintype.sum_prod_type]
  have hv (x : Site n) (i : I) : train (-p) a (x,i) * train p b (x,i) = a i*b i := by
    unfold train
    dsimp only; rw [cell_duality (-p),cell_inverse,cell_duality x]; field_simp
  simp_rw [hv]; simp
end row

def fpoint (V : Waves.Field G n) (b : G.ColorIndex) := (approached (d 1 n))*ᵥ fun i => V i b
lemma fpoint_add (U V : Waves.Field G n) (b) : fpoint (U+V) b = fpoint U b + fpoint V b := Matrix.mulVec_add ..
lemma fpoint_smul (V : Waves.Field G n) (z : ℂ) (b) : fpoint (z • V) b=z • fpoint V b := Matrix.mulVec_smul _ z (fun i => V i b)


def pairing (B : Bed) : Waves.Field G n →ₗ[ℂ] Waves.Field G n →ₗ[ℂ] ℂ where
  toFun v := {
    toFun := fun u => ∑ b, dotProduct (fpoint v b) ((approached (B.metric.acts n))*ᵥ fpoint u b)
    map_add' x y := by simp_rw [fpoint_add, Matrix.mulVec_add,dotProduct_add,sum_add_distrib]
    map_smul' t x := by simp_rw [fpoint_smul,Matrix.mulVec_smul,dotProduct_smul,smul_sum]; rfl }
  map_add' x y := by apply LinearMap.ext; intro z; simp [fpoint_add,add_dotProduct,sum_add_distrib]
  map_smul' t x := by apply LinearMap.ext; intro z; simp only [LinearMap.coe_mk,AddHom.coe_mk, fpoint_smul,
    smul_dotProduct, LinearMap.smul_apply,smul_sum]; rfl









end YM.Further.QuantumRates.Fiber
