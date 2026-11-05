import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Parameter
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Push.STATIONARY_UNIFORM.Paths

/-!
# Purchase analytic strips with external moves too

Entry costs; we just test uniform existence of scalar ceilings here,
separately priced in `fee` where used for the actual real comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Laurent Bloch RG Work.F07 Filter Matrix Function Topology
open scoped Classical BigOperators Topology
variable {σ s a b C D M:ℝ}{k α β ι : Type}[Fintype ι]
-- Routers to physical Momentums. `swings` keeps winding arithmetic full.
structure Shifted (σ C:ℝ)(f:Phase ι→Momentum): Prop where
  fits (p) : p∈strip σ→ Within C (f p)
  hol (p):p∈strip σ→DifferentiableAt ℂ f p
  swings (p):p∈strip σ→∀ x,∃ y:Cover,f (p+reciprocal x)=f p+reciprocal y
variable {f g: Phase ι→Momentum}
namespace Shifted
omit [Fintype ι] in
lemma widen (h:Shifted σ C f)(he:C≤D): Shifted σ D f:= ⟨fun p h' i=> (h.fits p h' i).trans he,h.hol,h.swings⟩


end Shifted

def Bought (s:ℝ)(f:Phase ι→ℂ):=∃ C:ℝ,Sold s C f
namespace Bought
variable {x y: Phase ι→ℂ}
omit [Fintype ι] in
lemma fixed (c:ℂ)(h:0<s):Bought s (fun _ : Phase ι=> c):= ⟨‖c‖,⟨h,fun _ _=>differentiableAt_const _,fun _ _ _=> rfl⟩,norm_nonneg _,fun _ _=> le_rfl⟩











variable [Fintype β]









end Bought
end YM.Primitives.TwoWave
