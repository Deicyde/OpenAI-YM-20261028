import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import YM.Next.SCHEDULE.Pre
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Probe
import YM.Push.FREE_RESOLVENT.Weights
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.LocalJet
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay

/-!
# A two-log test at a *physical* face

Include
color scales, orientation and cross-bond reading. Here just continuous
G-curvature of their pair, no scratch gauges or change of variables. The error inequality used below (in the issued gauge of `Local.hill`)
is valid on *all* such inputs, even our Gaussian tails. Prices G-first,
not with torus volume. This element for E ignores transports.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Arc
  
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure  Pressure.Stores Gaussian Tree  Bid
open   FreeResolvent    MeasureTheory 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {n c f : Side}

section pins

abbrev pins (p : Cell f) : Fin 4 → Bond f :=
  let x := p.1; let i:=p.2.val.1; let j:=p.2.val.2
  ![(x,i),(x+Lattice.step i,j),(x+Lattice.step j,i),(x,j)]



abbrev pairLog (G : Gauge) := LogArray G (Fin 4) × LogArray G (Fin 4)
def twoSides (x : pairLog G) (i : Fin 4) := G.lieExp (x.1 i) * G.lieExp (x.2 i)
def turn (x : pairLog G) := twoSides x 0 * twoSides x 1 * (twoSides x 2)⁻¹ * (twoSides x 3)⁻¹
def arc (x : pairLog G) :=
  let b i := x.1 i + x.2 i
  b 0 + b 1 - b 2 - b 3

-- Same calibration as linear faceCurl on representing the *sum*,
-- but here two actual factors, no equivalence even slightly off zero.











end pins
end YM.PhysicalNext.WeightedGaussianMarginal45C.Arc
