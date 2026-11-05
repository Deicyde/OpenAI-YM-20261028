import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Local

set_option autoImplicit false
set_option warningAsError false
set_option synthInstance.maxSize 1024

/-! E Frco/Fsct on the true variables. Exact comparison to Plate (work before
summation, not inferring each entry from two push identities). `e.book` SAME allocation
on both sides, and every address using k in each representation uses the same tag;
`tagRef` compensation also on the WHOLE physical choice. Exponent contains the real
tails. No equality to an uncut Hessian comparator or law. Integrability required when
using product-integral reorder (see also `purchased` which gives the Receipt along the
trajectory). All gates and normalizations are used on one plate. -/
noncomputable section
namespace YM.SectorTools.ActualScalar
open Function Filter Set MeasureTheory Matrix RG Wilson Lattice Pressure Pressure.Stores Precision Tree Push.SectorMeasure Presented
  Next.SectorChange Further GaussianScalar AnalyticBridge.ResetIncome SectorNext.Vacuum Next.Fluctuations.Sector
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {v : AnalyticBridge.GaussianFieldAlignment.Rates}
    (e : Plate G S) (R : Rep G f)

def baseCost (V : Config G c) := -Real.log (banker e.tube e.point V R.beta)





variable (h : Doors e) (A : Stores S) (k : S.Choices) (V : Config G c)










namespace Bought
variable {e}






end Bought
end YM.SectorTools.ActualScalar
