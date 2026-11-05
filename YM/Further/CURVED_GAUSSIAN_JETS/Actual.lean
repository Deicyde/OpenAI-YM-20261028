import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import YM.Further.CURVED_GAUSSIAN_JETS.Colors
import YM.Further.CURVED_GAUSSIAN_JETS.ShortGap
import YM.Push.CUTOFF_PROJECTORS.Equations


/-!
# Quoting this cut Gaussian-scalar interface at Directed

At consumers of genuine terminal/intermediate calibrated history, e.g.
the EXACT Wilson family in Spec.Final, not a construction of that Family
or even of its Directed. Use the actual predecessor's ell receipt for the
uniform cut/uncut flat comparison, *before* the business of proving
estimates for the selected Gram, Gaussian identification, and assembling
the output. Order by landed smoothing stage. Even the supposedly flat-tag
reference requires its OWN determinant and invariance proof; do not
pay alpha with that scalar or throw away ½Tr log(1+S) for a selected C.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Actual
open RG Supply Shoot Precision Wilson Input  SectorNext.Vacuum 
open Function Filter MeasureTheory Matrix Lattice Tree Pressure Flat Progress.StationaryScenes Bid
open Green (link address)
open Rows (Bill)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology
variable {G : Gauge} {f c : Side} {S : StepData c f}

def initial (W : PathData G) (c : Clip) (N : ℕ) (F : Forest S.ratio) := Tint.row G.ColorIndex (Cut.base W c N S F)
def ideal (B : Bed) (F : Forest S.ratio) := Tint.row G.ColorIndex (history S F B)




structure Comparison (p : Prices) (F : Forest S.ratio) (B : Bed) (v : Clip) (W : PathData G) (N : ℕ) (C : ℝ) : Prop where
  cut : Fits (address F) p (initial W v N F)
  flat : Fits (address (G:=G) F) p (ideal B F)
  difference : Bill (address F) p.width (initial W v N F-ideal B F) (Cut.expense C p.width * Real.exp (-p.width*N))



section planned
variable {C : Sheet G} {D : Rolls C} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {J : ChartRatio G} {K : MapPrices} {O : PostCost D} (A : Input.Directed G I J K O)




end planned
end YM.Further.CurvedGaussianJets.Actual
