import YM.Push.LOOP_COEFFICIENT.Frame.Environs

/-!
# Reading both fine and joint input stencils in native fields
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Matrix Filter Set Lattice Laurent RG Bloch Precision Exterior Pressure Wilson Gauge YM.Branch Block
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {P : Patch} {C : KernelChoices} {c f : Side}

def logs (v : Interior P G → ℝ) (i : Edge Cover) : G.Color := WithLp.toLp 2 fun j => locate P v i.1 (i.2,j)
@[simp] lemma logs_zero (i : Edge Cover) : logs (0:Interior P G → ℝ) i = 0 := by ext j; change locate _ _ _ _ = (0:ℝ); unfold locate; split <;> rfl


def jumps (v : LocalField P G → ℝ) (i : Satellite) : G.Color := WithLp.toLp 2 fun j => v (.inr (i,j))
def bondVar (v : Outlook P G → ℝ) (i : Axis) : G.Color := WithLp.toLp 2 fun j => v (.inr (i,j))








-- The incoming root log. Evaluate additive path integrals at shifted offsets.
def cloudSite (P : Patch) (j : Satellite) := P.L.val • location j
def forceLink (j : Satellite) (v : Interior P G → ℝ) (i : P.Points) : G.Color := WithLp.toLp 2 fun s => -avg (fun k : P.Points => avg (fun o : Lattice.Order => linkSum (fun e : Edge Cover => logs v (e.1+cloudSite P j,e.2) s) i.val (route i.val k.val o)))
def wind (j : Satellite) (v : Interior P G → ℝ) : G.Color := WithLp.toLp 2 (fun s => forceLink j v P.center s - ∑ i, P.weight i * (forceLink j v i s))




end YM.Push.Loops.Frames
