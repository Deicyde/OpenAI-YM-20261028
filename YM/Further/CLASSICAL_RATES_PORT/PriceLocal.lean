import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Rebase
import YM.Extra.WILSON_STARTUP.Engine
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Rack
import YM.Next.SCHEDULE.Chorus



set_option warningAsError false

/-!
# Fitting the Wilson-top Rate invoice: pricing / feasibility example

One OPTION illustrating deployment even with the new rates. Not used by the
main seam. In generating this Horizon we opt for the known `WilsonStartup`
local Bed boundary condition so can actually cash the top invoice. Use the
existing isometric retarget (which does NOT promise the T.T field) inside
linear data preparation, but also show we can take care not to overwrite the
T.T (potentially crucial for the inherited and loop calculations). Output-
price reservation *before* U, etc., with enough comparisons to pay all this
in both radius and caps. Doesn't claim this change of the top realizes, for
instance, the particular positivity algorithm in the text. Targets the
implementation's actual `Horizon.Suffices` and Service obligations here.

**This doesn't port across unequal Beds!** Use the resulting M from the
BEGINNING in purchasing Service, proving step estimates, measuring PathData
and generating one matching family. The top Bed can differ from what's in the
raw kernel auxiliary Horizon. No upgrade of Service, Present or Rack to M
claimed. No upgrading an arbitrary request about some other Horizon or the
ker/paths after proving some kinetic matches. Scope ends at `Initial`; in
particular not even proving `QuantumOwed` sensible automatically on this M.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ClassicalRates.PriceLocal
open Filter Function Lattice Wilson RG RG.Supply Precision Bid Extra.Iteration
    Tree  WilsonStartup
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}

section location
variable {a : Levels G}

/-- Explicit linear commitments for this top option. NOT `Bid.Retained`! -/
structure Keeps (V M : Horizon a) : Prop where
  boundary : Change.Overlay V M
  columns N m : m < N → (V.towers N m).T=(M.towers N m).T







def together (A B : MapPrices) : MapPrices where
  α := fun i => min (A.α i) (B.α i)
  η := B.η
  Ω := fun i => max (A.Ω i) (B.Ω i)
  alpha_pos i := lt_min (A.alpha_pos i) (B.alpha_pos i)
  eta_pos := B.eta_pos




end location

section cheap
variable {S P : Sheet G} {a : Levels G} (h : Upgrade S P) (ha : a.clock.stage=P.profile)

include h ha





end cheap








end YM.Further.ClassicalRates.PriceLocal
