import Mathlib
import YM.AnalyticBridge.RESET_INCOME_PORT.Plate
import YM.Next.UV_STRESS.Across
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.PRICE_COMPILER.Suppression
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Leases


set_option warningAsError false

/-!
# What a true LFR ticket pays at Split

Optional coarser calculation, e.g. for deciding whether even very-high
seed sectors are disposable with this price.

Real κ/choice data of
`Quota`, selling against the very same common ledger and one unnormalized
remainder.

DON'T spend this instead of local numerator tests claiming it a
normalized Gaussian suppression of all the omitted addresses in any useful
Split; in particular arbitrary large period alone wouldn't insure the
`freight` conclusion from the leading terms.

Can use a closer analysis (at
`Plate.expense/Coupon`, or log version with all Stores billed in reassembly).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome.BulkFare

open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange SectorNext.Remainder
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
    (e : Plate G S) (R : Rep G f) (V : Config G c) (u d κ : ℝ)

def meter := Mode.size .shielded G S.patch.L e.x

/-- Here `u` is the proposed log prediction at V, not a new partition
choice. Relative to the log **outside** leaves the factor billed against
the gas. One necessary new comparison if using this approach will be
against `surface`, in general can cost powers C_L^volume. kappa is earning
seed-price in the very different units here. -/
def surface := 2* (nf f : ℝ) + (nt e.forest : ℝ) * Real.log ((d * meter e ^ dim G) / spare e.chart R.beta) +
  Real.log (Real.sqrt e.Flat.det) + Real.log (outputReserve .shielded true e.tube e.x R.beta V) -
  Real.log (banker e.tube e.point V R.beta) - (u-e.outside R V)

def cash (n : ℕ) (H : ℝ) (A : Stores S) := surface e R V u d -
  coin G S.patch.L H n e.x * A.shares - seed G S.patch.L e.x κ R.beta A.shares/2

variable {e R V κ d u} {H C γ : ℝ} {n : ℕ} {A : Stores S}








end YM.AnalyticBridge.ResetIncome.BulkFare
