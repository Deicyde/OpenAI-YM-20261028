import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.ODE.ExistUnique
import YM.Next.MAXWELL.System
import YM.Pressure.Seeds


/-! # Columns: square full-rank at generic two points, from the same labels -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder Matrix
variable {G : Gauge} {j k n d : ℕ}





section basis
variable (F : Labels.Frames G) (d : ℕ)

def actual (a : (F.level d).Index) : (Model F).Field d := (Model F).project d ((F.level d).coords ((F.level d).basis a))



end basis

section density
variable (F : Labels.Frames G)
abbrev W := Model F











end density




end YM.Maxwell.Free
