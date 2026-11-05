import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Blocks
import YM.Push.CUTOFF_PROJECTORS.Signed
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Remainder
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Bills

set_option warningAsError false

/-!
# Place the qvoid flags, for K occurrence estimates

 and . Refine the payment factorization: the qvoid
products here are absorbed from `owing{,Full}`, *not* deduced
from absence of seeds. Estimates with `oblige` retain them. All
arguments reconstructed at *the same* substitution. Keep all tests
in and near K supports and history tests of `extraTest` inside the
remaining account. No deletions of enabled K addresses because of a
branch or non-wrapping guess. Note the coverage at fine flags in
this file is separate from the already compulsory output flags and
fine seed predicates in `packet`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus.Cover
open Function Set Filter Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange MeasureTheory Metric Presented Matrix LabelSum
open YM.SectorNext.Remainder (coin)

open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}



variable (R : Rep G f) (b : Finset ℕ) (U : Config G f) (X : Finset (Site f))

/-- *Original* supports. -/
def outside (i : Site f) := i ∉ b.biUnion fun j => (R.activities.forced j).support

def clear := ∀ i∈X, outside R b i → i∉ RG.flags R.p.threshold U













variable (T : Tube G S) (x w : ℝ) (V : Config G c) (A O : Stores S) (k : S.Choices)
    (F : Forest S.ratio) (D : ℕ) (p q : Chi) (J : ChartRatio G) (d : ℝ)
    (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (C : Gaussian.Table (Rows.In x A F (G:=G))) (B : BudgetPoint)


















end YM.AnalyticBridge.Annulus.Cover
