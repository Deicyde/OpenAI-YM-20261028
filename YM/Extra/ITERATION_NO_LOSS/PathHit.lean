import YM.Extra.ITERATION_NO_LOSS.Geometry

/-! Charging arbitrary halo and exponent reserves on the actual canonical
terms simultaneously with the finite-order derivatives (each in the
orientation where its configuration and footprint are read). -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Shapes
open Function Lattice Lattice.Corona RG Wilson Finset Laurent 
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {k : ℕ}

def broad (s B : ℕ) (A σ : ℝ) := 16*(pad s:ℝ)*A ≤ (B:ℝ)*σ











end YM.Extra.Iteration.Shapes
