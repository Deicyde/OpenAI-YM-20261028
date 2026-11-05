import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Borel

set_option warningAsError false

/-!
# Conditional Gaussian integral with ancestors held fixed

Consumer distinguishes:

* The whole intact push integrand at $(V,A,k)$, whose exact equality
  is in `Change`.
* Local payment and procurement on every actual packet used there,
  applied here to a *single* (possibly merged) O in such sector. Norm
  kernel, with explicit outstanding change-price jobs in `page` before
  any cancellation by the corresponding denominator jobs. In particular
  this isn't a point bound on the entire integrand with constants
  depending only on H et al.

The remaining integral really exists; we keep it guarded (the packet
support indicator in it needs to travel in future uses!). Simply deleting
the packet facing an unpriced quadratic, hard constraints, etc under the
Gaussian is not justified. No Holder-independence trick, or billing the
scalar by seed prices. Clouds can be chosen on the same fog; arbitrary
m/C allowed parametrically here whenever the hypotheses supplied on
that choice. Fixed period compact bounds used in proving mere
integrability are never used in estimates as if uniform.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus
open Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange Set MeasureTheory Metric Presented Matrix
    Next.Fluctuations Borel
open YM.SectorNext.Remainder.Scales
open YM.SectorNext.Remainder.Affine
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x w : ℝ) (V : Config G c)
    (A O : Stores S) (k : S.Choices) (F : Forest S.ratio) (D : ℕ) (p q : Chi) (J : ChartRatio G) (d : ℝ)
    (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (C : Gaussian.Table (Rows.In x A F (G:=G))) (R : Rep G f) (B : BudgetPoint)

/-- Ancillary account after using packet payment and pulling out the
full coarse base, restricted to those Gaussian/held assignments where
it is *used*. -/
def page : PaintBox G A x F → ℝ :=
    let P := Function.uncurry (packet T x w V A O k F D p q J d R.beta m)
    (Function.support P).indicator (fun i => owingFull T x w V A O k F D p q J d m C i.1 i.2 R B)









/-- The estimate delivered on precisely these identities (not
including integrability once one drops guards in `page`). -/
structure Integrated (n : ℕ) (H κ : ℝ) (hw : 0<w) (ht : 0<fiery G x S.patch.L) : Prop where
  packetBill :
    let μ := (piHaar G (Frozen A x F)).prod (Gaussian.cloud C)
    let u := uncurry (packet T x w V A O k F D p q J d R.beta m)
    Integrable u μ ∧ (∀ i, Real.exp (valuation O H n x G)*‖u i‖ ≤ remaining O G x κ) ∧
      Real.exp (valuation O H n x G) * ∫ i, ‖u i‖ ∂μ ≤ remaining O G x κ
  paid :
    let μ := (piHaar G (Frozen A x F)).prod (Gaussian.cloud C)
    let v := page T x w V A O k F D p q J d m C R B
    let f₀ := Fintype.card S.Choices * Real.exp (salted T x V A k F J R.beta C)
    let s := sleeves T x V k A R (shots S x) F (p.profiles G S x w hw ht) q J d B C m
    Integrable v μ ∧ Integrable (uncurry s) μ ∧
      (Real.exp (valuation O H n x G) * f₀) * ∫ i, ‖s i.1 i.2‖ ∂μ ≤ remaining O G x κ * ∫ i, ‖v i‖ ∂μ


end YM.AnalyticBridge.Annulus
