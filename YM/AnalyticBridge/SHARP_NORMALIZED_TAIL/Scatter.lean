import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Packets

/-!
# Census criterion for the extra read check

For scattered `Registers.merge`, not an extra estimate assuming a variant
of `leftOver`. Works also with no packets. Another producer has to check
that `Spells` covers the physical Y,Z stencil; here for taking an income
it suffices additionally to check the energy reads of each packet. No
claim those are the desired local functions after dropping defaults.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Drain
open Filter Function Lattice RG Pressure Pressure.Stores Wilson Tree MeasureTheory
open Next.Fluctuations.Sector Next.SectorChange SectorNext.Vacuum.ReLog
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented Finset Inventory Almanac Presented
open Precision SectorNext.Remainder SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius YM.Push.SectorMeasure

variable {c f : Side} {G : Gauge} {x W : ℝ} {S : StepData c f} {T : Tube G S} {P : Teller G}
  {R : Rep G f} {D : Allocation G S x W} {F : Forest S.ratio} {V : Config G c} {L : Almanac T D R F}










variable {E ι : Type} [DecidableEq E] {K : Cards S ι E} {H : Roster L V K} {ψ : H.Script}
    {θ : ℝ} {α : ℕ} (N : Staple H θ α)

abbrev Parcel (Q : Finset ι) := Σ i : ↥Q, ↥(N.stems i)





end YM.AnalyticBridge.Sharp.Drain
