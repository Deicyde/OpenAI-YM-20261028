import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import YM.Next.SCHEDULE.Blocks
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Change


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Use over varying V without a regularizing assumption on sector centers

Show Borel envelope / cost equality of the transformed *marginal*, even
for its absolute version (after determinant and scaling/sieve prefactors).
Thus may integrate against output Haar or pricing test. This method does
not assert joint measurability on (V,Y,Z) -- don't interleave Z integrations
with coarse test operations from these facts -- nor volume-uniform costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian Rows
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented

open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {w : ℝ}

variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (A : Stores S) (R : Rep G f)
  (W : Stencils S) (F : Forest S.ratio) (D : Allocation G S x w) (q : Chi) (J : ChartRatio G) (d : ℝ)
  (C : Gaussian.Table (In x A F (G:=G))) (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))

def station (g : ℝ → ℝ) := prefactor S G R.beta * J.scale ^ Fintype.card (Active A x F) * chartCost C (coupling R.beta) *
    ∫ Y, (∫ z, g (dyed T x V k A R W F D q J d C m Y z) ∂cloud C) ∂piHaar G (Frozen A x F)




end YM.Next.SectorChange
