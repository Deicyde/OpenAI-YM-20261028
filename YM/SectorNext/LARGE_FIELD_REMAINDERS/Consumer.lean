import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.PSeries
import YM.Next.BOUNDARY.Coordinates
import YM.Next.SCHEDULE.Blocks
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Absorb
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Leases


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# At a committed unmarked step

Specialize the estimates to literal `Lives` & the input side of `Program.advances`,
with same baked path/tags. True represented remainder bill AND charge there with
Ringing and Prepared (in fact use `Transmitting`: same κ is important, doesn't
follow just from unspecified usage of a Ringing). `Testing.proceeds` uses retained
Horizon from the same Directed; show also how to use that part of FREE's output
earlier with path hypotheses if scheduling such witnesses. Not proving them or that
the global history witnesses exist; this service usable even before Γshooting or
constructing the planned path algorithm. Take actual extra costs even at incoming
coefficient labels. v and denominator caveats, see Grant. Includes example
selling even the whole relative-to-exp(v) L1 push estimate (not density transfer).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Consumer
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Pressure.Testing
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Metric Oriented Presented Tree RG.Supply
  YM.Input RG.Shoot Next.Scheduling  
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {G : Gauge}







-- ordinary record with EXACT costs. `vol` only with enlarged Ls and Simple
-- (for control of `shore`, not needed to produce the record).
structure Quota {c f : Side} {S : StepData c f} (R : Rep G f) (x W κ : ℝ)
    (T : Tube G S) (H : ℝ) (n : ℕ) (C γ D : ℝ) : Prop where
  grant : PointCharge T x W κ
  portions (F : Forest S.ratio) (d : Allocation G S x W) : PortionCost d F T κ R
  book (V : Config G c) (F : Forest S.ratio) (d : Allocation G S x W) :
    (∀ A,0≤rent d F V A .shielded C γ D) ∧ (∑ A, rent d F V A .shielded C γ D) ≤ 1
  deduct (V : Config G c) (F : Forest S.ratio) (d : Allocation G S x W) (A : Stores S) :
    let M := rent d F V A .shielded C γ D
    let O := outputReserve .shielded true T x R.beta V
    let E := seed G S.patch.L x κ R.beta A.shares
    let v := coin G S.patch.L H n x * A.shares
    Real.exp v * earn S G x κ R.beta A.shares * leftOver d F T R A V ≤
      Real.exp R.scalar * shore S G F .shielded R.beta x D*Real.exp (-E/2)*O*M ∧
    (G.Simple → VolPrice G S.patch.L → Real.exp v * ‖cutEntry d F T R A V‖ ≤
      Real.exp R.scalar * ice G S.patch.L x ^ nf f * Real.exp (-E/2)* O * M)

variable {s : Survey G} {q : Quote} {v : ℕ → ℕ} {K : MapPrices} {D : Rolls (s.paper q v)} {T : Protection D} {V : Delays T} {R : Radios K D}
-- K needs implicit


end YM.SectorNext.Remainder.Consumer

-- Demonstrate use on full torus and on a physical tail.
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Consumer
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Pressure.Testing
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Metric Oriented Presented Tree RG.Supply
  YM.Input RG.Shoot Next.Scheduling  
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {G : Gauge} {c f : Side} {S : StepData c f} {R : Rep G f} {T : Tube G S}
  {x W κ C γ D : ℝ} {n : ℕ}





/-! Use earlier with retained FREE horizon even before achieving Directed.
 Demands PathData.Bounds and Attached on that horizon; must ensure any caller
 purchases same Κ and W. `Present` alone doesn't certify these path bounds!
 This is nonlinear use of Deep and exact defect identities, not a claim about
 a flux or evolution on the free/continuum side. See Hardware.through_launch.
-/
variable {s : Survey G} {q : Quote} {v : ℕ → ℕ} {K : MapPrices} {D' : Rolls (s.paper q v)} {Θ : Protection D'}
variable {W : Delays Θ} {Y : Bar W} {Z : ChartRatio G} {Q : PostCost D'} {I : Wait Y} {R0 : Radios K D'}


end YM.SectorNext.Remainder.Consumer
