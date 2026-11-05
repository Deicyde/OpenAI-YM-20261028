import YM.Bid.Station
import YM.Push.STRESS_FLUX.Matching

/-!
Fine-mesh Wilson flux density as a one-point step function (piecewise
constant ONLY in stress position; round all spectators on the same mesh).
Uniform separated support and estimates for smooth windows. On sufficiently
large periods exactly equal, without an auxiliary normalization, to the
finite boundary operator from `Discrete`.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.StressFlux.Layer
open Matching Function Set Filter Lattice Wilson MeasureTheory Extraction Analysis Metric
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {R : Schedule} {p N n : ℕ} {G : Gauge} {C : Family G} {χ : E4 → ℝ} {V : E4 → E4} {a b : Axis}

def pack : E4 ≃ₗᵢ[ℝ] Points 1 :=
  { toFun := fun y => points fun _ => y
    invFun := fun y => y 0
    left_inv := fun _ => rfl
    right_inv := fun y => PiLp.ext fun i => congr_arg (y ·) (Subsingleton.elim 0 i)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' y := by simp [PiLp.norm_eq_of_L2,Real.sqrt_sq] }

def replicate {α : Type*} : α ≃ (Fin 1 → α) where
  toFun y _ := y
  invFun q := q 0
  left_inv _ := rfl
  right_inv _ := funext fun i => congr_arg _ (Subsingleton.elim _ i)






def node (N : ℕ) (x : E4) := tag (R.a N) (address (R.a N) (pack x)) 0










end YM.StressFlux.Layer
