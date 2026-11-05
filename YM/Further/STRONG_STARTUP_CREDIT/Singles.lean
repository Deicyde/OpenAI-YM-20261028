import YM.Extra.WILSON_STARTUP.Store

set_option warningAsError false

/-!
# The actual top K's: an unused exponent from the merger

In this Wilson startup method (`YM.Extra.WILSON_STARTUP`), attachments
are zero. This does NOT mean one should use a smaller alphabet. Instead
analyze which of the **fused** addresses can have nonzero vacuum weight.
They are among singleton pellets, and these cost no exponent in the
merger! In particular can use Allows *unchanged* for the Multi +1 ask.
This part of the estimate doesn't even need a cutoff-size bound or the
E grant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.StrongStartup
open Function Filter RG Lattice Wilson WilsonStartup WilsonStartup.Start Ovens Ovens.Pipes
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {b : BudgetPoint} {c : Clip}














/- Nonzero implies no right, but possibly many lefts? In a Pellet,
paths of patch overlaps would have to connect them. The stored lefts
already have pairwise disjoint supports. Thus exactly one.
-/


/- The payment on the whole alphabet, including all spare E and K
addresses on which startup currently spends nothing. It's the very same
function k for every β, not a price chosen after substituting a period's
coupling. -/
def kCoin (G : Gauge) (n : Side) (b : BudgetPoint) (σ κ : ℝ) :=
  Function.extend (single G n) (fun i => Real.exp (-κ)*cash n b σ i) 0

variable {l σ κ γ : ℝ}













end YM.Further.StrongStartup
