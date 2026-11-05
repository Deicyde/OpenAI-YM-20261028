import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Currency
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sky
import YM.Progress.DIRECTED_RECIPE.Economy

set_option warningAsError false

/-!
# Budgeting the quadratic inverse discrepancy in *actual* adjustment

The remaining Y-linear & constant charges are not set to zero. Separate them
by probing the z-even positive-degree part for this cost, no need to assume
that the *full* adjusted log is smooth at the boundary of all sector tests in
order to price this part. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix MeasureTheory
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Gaussian FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k n : ℕ} {σ d r C x η g b : ℝ} {ι α : Type} [Fintype ι]





/-- Evaluate a D^tD discrepancy letter in the z exponent (all ordered
positions are kept; collapsed by summation only in this receipt). -/
def tariff (z : Vec ι) : Matrix ι ι ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ({
  toFun M := (z ⬝ᵥ (M *ᵥ z))/2
  map_add' M N := by simp [add_mulVec,dotProduct_add, add_div]
  map_smul' r M := by simp [smul_mulVec,dotProduct_smul,mul_div_assoc] } : Matrix ι ι ℝ →ₗ[ℝ] ℝ)

def duet (T : Tube G S) (x : ℝ) (t:S.Choices) (A : Stores S) (F : Forest S.ratio) (z : Prices G (Active A x F)) (V : Config G c) : ℝ :=
  tariff z ((fog A F T x V t)⁻¹ - Rows.gram T x V t (shots S x) A F)

-- adjustment identity uses SAME frozen values and center, `q` and D, signs.


variable (P : Patch) (p : Teller G) (hC : 0<C) (hr : 0<r) (hd : 0<d) (hp : Sky G p P x C r k d b η g) (he : Cash G P.L x)
variable (T : Tube G S) (hP : S.patch=P) (hT : p.Funds S T) (hg : 100*(1+radiusB x)≤c.val)
variable (A : Stores S) (F : Forest S.ratio) (t:S.Choices) (z : Prices G (Active A x F))
  (l : List (Directions G c)) (o : Site c) (j : ℕ) (hl : l.length ≤ k) (h : Bends o l x j)
include hp hP hT hg hr hl


include hC hd he h



end YM.AnalyticBridge.Covariance
