import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Unnormalized, absolute volume-uniform price before later sector operations

Use ONLY at the denominators this says: NO vacuum division (penaltyZ already
in kernel is paid here). Includes actual interacting cut sector and full
integral as in Presented. Crude split of vacuum-energy prefactor: R.scalar
can be arbitrary, don't sell an absolute bound independent of it.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial  Next.Fluctuations  Scales Metric  
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical  ENNReal

variable (G : Gauge)

def ambient := Module.finrank ℝ G.Mat



--

def ice (L : Side) (x : ℝ) := Real.sqrt (g G L x)



/-- Sufficient L-threshold, not necessary; used just to simplify even the
volume bills pre-vacuum. Independent of W, scheduling, or Λ. -/
def VolPrice (G : Gauge) (L : Side) : Prop := 8*(ambient G+1) ≤ L.val^4



end YM.SectorNext.Remainder
