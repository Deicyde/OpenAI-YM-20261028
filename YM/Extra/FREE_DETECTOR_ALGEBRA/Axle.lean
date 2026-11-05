import YM.Extra.FREE_DETECTOR_ALGEBRA.Forest
import YM.Extra.FREE_DETECTOR_ALGEBRA.Height
import YM.Extra.FREE_DETECTOR_ALGEBRA.Rank



set_option warningAsError false

/-! Homogeneous Field elements after **exact** detector quotient. Norm or
Choice of basis not presumed orthogonal between stages. Inclusions under
any DiffPlan from separated words automatically read by the same Wick label.
Use parity to eliminate vector perturbations that preserve the weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels SphereTest   Ward Climb MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder Matrix

variable {G : Gauge} (F : Frames G) {i j k n d e : ℕ} {x y : E4}

local notation "W" => Table.Field (freeTable F)
local notation "T" => freeTable F
local notation "γ" => writes F








-- weight eigenspaces on the Field (including units)
def AtWeight (p : W d) (j : ℕ) : Prop := Exact (γ d p) j







-- weighing preserves cap












end YM.Extra.FD
