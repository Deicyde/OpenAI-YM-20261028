import Mathlib
import YM.Next.FREE_KERNELS.Signal
import YM.Next.UV_STRESS.Across
import YM.Push.ABSOLUTE_SUMS.Delay
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.PRICE_COMPILER.Pre

/-! Post-L delay for the complete forced dictionary, before and after §freset. Actual
strong-gain supply from the Cab point charge (caller must preserve it, not reassign κ afterward).
No earnings here of the pending auxiliary projection/alignment or the score estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc.Rate
open Function Filter Set Lattice Wilson RG Pressure Push.AbsoluteSums Push.PriceCompiler 
  
open scoped Topology BigOperators

variable (G : Gauge) (L : Side) (S : Stage)

def stamp (κ x : ℝ) := Delay.hatWin G L (κ/2) (1/4) x
def intense (g : ℝ) := Real.exp (-(g/2))














end YM.PhysicalNext.InterpolatedSecantsFc.Rate
