import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.SCHEDULE.Layers
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.STATIONARY_UNIFORM.Continue
import YM.SectorNext.VACUUM_NORMALIZATION.Factors
import YM.SectorNext.VACUUM_NORMALIZATION.Noise

set_option warningAsError false
/-!
# Honest size in the scalar ledger if using the station comparator

Per-coarse-site price ANY period and depth at a calibrated call. Flat
Hessian *itself* (not a shifted partition), Gram dimension, beta-band
scale and the explicit missing term against the true normalizer.
This is an extensive scalar comparison, no E-jet or coupling-repair
claims. Avoid using as though bounding sparse marker ratios.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.QuantumRates.Accounts.Price
open Function Filter Lattice Wilson RG RG.Supply Precision Exterior Tree  Bid
open SectorNext.Vacuum  Push.Uniform Matrix Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {L f : Side} {S : StepData L f} (F : Forest S.ratio)

def spectral (G : Gauge) (Y : ChartPrices) := Panel.amount (Y.gap/2) (Y.value*(townCost G*countCost Y.width))



-- Absolute reference price without keeping path ontology after this bound




variable (X : History G) (M : Menu G X.levels.clock.stage X.levels.clock.kernel) (O : ChartRatio G)

/-- Pay uses BEFORE extracting a particular period. Cost depends level
and clock data, not depth N or the actual realized paths. `p=0` op used
as placeholder only; actual per-period p does not affect these
query fields. -/
def budget (i : ℕ) :=
    let β := X.levels.clock.hatBeta (i+1)
    4*shellBill G (X.levels.clock.op i 0) (2*β) + (3*((X.S.block i).val:ℝ)^4+1) *
      (max |Real.log (gaussLink O (2*β))| |Real.log (gaussLink O (β/2))| +
        (Module.finrank ℝ G.Color:ℝ)*spectral G (fare M i 0)/2)


end YM.Further.QuantumRates.Accounts.Price
