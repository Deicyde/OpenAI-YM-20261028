import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Voucher

/-!
# Exact single-packet splice at `dyed` on a fixed real step

Use `full_price` before or alongside.

Expose exactly the (possibly still
extensive) payment demands on other terms.

No analiticity or
Mayer-expansion claim; instead define remainder determinant purely
algebraically with caller's L for the compulsory local term's *part*.

This file pointwise at all held and Gaussian arguments.

And get the
corresponding exact normalized-Gaussian and shell price *integral* (of
unnormalized density, not saying we know an estimate on it).

K labels in the sum genuine activities list, summability on intact
steps. Uniform tag convention division exact, not switching conventions
implicitly. `sieve` and `banker` both actual. Keep all other scalar
and activity overhead. No invariance under changing Forest needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations Next.Fluctuations.Sector
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented LabelSum
open SectorNext.Remainder.Affine Harvest Dress
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (O A : Stores S) (T : Tube G S) (x W : ℝ) (V : Config G c) (k : S.Choices) (q : Chi)
  (d : ℝ) (J : ChartRatio G) (p : Rep G f) (F : Forest S.ratio)

variable (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F))
  (L : Bond f → ℝ) (m : Mean (G:=G) A x F)
variable (C : Gaussian.Table (Rows.In x A F (G:=G))) {n : Type} [Fintype n] [DecidableEq n] (flat : Gaussian.Table n)
variable (X : BudgetPoint)

def estate := let Q := Rows.gram T x V k (shots S x) A F;
  -(1/2)*(Real.log Q.det - Real.log flat.det)+(1/2)*Real.log (1+(Q*C-1)).det

















section authorized
variable (hW : 0<W) (hx : 0<fiery G x S.patch.L)





end authorized
end YM.AnalyticBridge.AnnulusRatioInsertions
