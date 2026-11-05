import YM.Push.LOOP_COEFFICIENT.Frame.Deposit
import YM.Push.LOOP_COEFFICIENT.Frame.Fixtures

/-!
# Initial velocities in the weighted-center convention
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Guard
open Function Filter Set Matrix Lattice Laurent RG Wilson Precision Exterior Pressure Complex Gauge Block Portal Frames
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {P : Patch} {K : KernelChoices}
abbrev Vector (P : Patch) (G : Gauge) := LocalField P G → ℝ
def fly (v : Vector P G) (t : ℝ) : World P G := (0,t • v)
def value (v : Vector P G) (j : Satellite) (i : Edge Cover) := logs (v ∘ Sum.inl) (i.1+cloudSite P j,i.2)








def loss (v : Vector P G) (j : Satellite) (x : P.Points) := YM.Branch.avg fun y : P.Points => YM.Branch.avg fun o : Lattice.Order => linkSum (Guard.value v j) x.val (route x.val y.val o)
def rebate (v : Vector P G) (j : Satellite) (x : P.Points) := weighted P.weight (loss v j) - loss v j x


end YM.Push.Loops.Guard
