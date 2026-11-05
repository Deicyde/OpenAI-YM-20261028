import YM.Planned.PRIMARY_INTEGRAL_295.Bazaars
import YM.Planned.PRIMARY_INTEGRAL_295.Junction

/-! # Comparing normalized b chart on Journey Panels at true torus operators

Require b(y) chosen with path and paid through physical normalization
for this query with parameters independent of tree tag. Later propagate
Q-model from this theorem. Membership on WHOLE used addresses including
mask paths. Not invoking any C^∞ on field growth, order k sufficient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Bazaars
open Function Filter Set Metric Lattice RG Wilson Labels Source
open Precision Exterior Bloch Work.F08 Tree Next.Free Carrier Place Dunes Streets Porous
open Junction Oval WardBin.Lies
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {c f : Side} {S : StepData c f} {G : Gauge} {T : Finset Cover} {n k : ℕ}



variable (T) (b : Panels n → Dir G c) (S) (W:Lines S.ratio.count)

def b_zero := aboard G c (b 0)
def b_call (i:Fin n) := aboard G c (fderiv ℝ b 0 (cart i))



structure Hint (r:ℕ) (R C : ℝ) : Prop where
  price : Guard (b_zero b) (b_call b) r R
  extra : 0 ≤ C ∧ ∀ i : ℕ,1 < i → i≤n → ‖iteratedFDeriv ℝ i b 0‖ ≤ C


end YM.Planned.PrimaryIntegral295.Bazaars
