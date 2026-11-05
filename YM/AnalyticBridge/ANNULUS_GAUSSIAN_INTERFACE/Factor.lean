import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.LocalLog
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Rows
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ledger



set_option warningAsError false

/-!
# Reaccounting `dyed`

Same (T,F,x,k,V,A,m,C,d) in *every* factor.

Keep linear,
quadratic and relative determinant remainders explicit; and the scalar
with actual nFree, never pricing it by a packet bound.

All local visits
include flags, cost via D=profile allocation on the same fibers.

This factorization step needs no series expansion. For a full-base
formula one also factors the input scalar and restores the output sieve
and path tails; a version `shuttle_full` for that is included. Not
moving E or K across flags; qvoid still EXACT globally in `exposed`,
can refine per K occurrence (separately from this energy calculation).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus
open Function Lattice RG RG.Patch Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
  YM.Push.SectorMeasure Oriented Presented Precision Exterior Bloch Next.SectorChange MeasureTheory Matrix
open YM.SectorNext.Remainder.Affine
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Tube G S) (x w : ℝ) (V : Config G c) (A O : Stores S) (k : S.Choices)
    (F : Forest S.ratio) (D : ℕ) (p q : Chi) (J : ChartRatio G) (d β : ℝ)
    (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (C : Gaussian.Table (Rows.In x A F (G:=G)))
    (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F))

/-- `p` chooses the actual Allocation profiles, `q` determines the
actual chartMean and broad profiles. Hard flags still tested. -/
def releaseOn (X : Visits S) (N : Finset (Active A x F)) :=
    let y := tape (m Y + coupling β • z)
    let U := physical A F V Y y
    jacob J q d N y * (border X A p x w U V k * tagRate X k U)

def labor (X : Signed → Window S) :=
    let u := m Y
    let a := u + coupling β • z
    let U := physical A F V Y (tape a);
    -β * averaged (fun s => debris T x V k A F q d Y a U s (X s)) -
      averaged (fun s => squares T x V k A F q d Y u s (X s)) / (coupling β)^2

def quotaCharge (N : Finset (Frozen A x F)) := -(N.card:ℝ)*Real.log (spare J β)

def shiftCharge :=
    let Z := Rows.gram T x V k (shots S x) A F
    (1/2:ℝ)*Real.log (1+(Z*C-1)).det

/-- Outstanding Gaussian action (in addition to `labor` complement),
needs independent estimates *under the same cloud* to price.
`Rows.adjustment` has `-Rows.guide...` which is split in labor. -/
def shiftRisk :=
    let Z := Rows.gram T x V k (shots S x) A F
    (Rows.eta T x V k (shots S x) A F q d Y (m Y) (coupling β) ⬝ᵥ z) + (z ⬝ᵥ ((C⁻¹-Z)*ᵥ z))/2

def packet := releaseOn x w V A k F p q J d β m Y z (Visits.near O D x) (openAt O A D x F) *
    Real.exp (labor T x V A k F q d β m Y z (inner O D x) + LocalLog.write T x V A O k F D +
      quotaCharge x A F J β (freezeAt O A x F))

def outsider := releaseOn x w V A k F p q J d β m Y z (Visits.near O D x).unattended (openAt O A D x F)ᶜ *
    Real.exp (labor T x V A k F q d β m Y z (fun s => other (inner O D x s)) + LocalLog.LaterCost T x V A O k F D +
      quotaCharge x A F J β (freezeAt O A x F)ᶜ + shiftCharge T x V A k F C + shiftRisk T x V A k F q d β m C Y z)

def owing (R : Rep G f) :=
    outsider T x w V A O k F D p q J d R.beta m C Y z * exposed R (till x) (physical A F V Y (tape (m Y + coupling R.beta • z)))

/-- Ledger scalar cost left INSIDE sector/tag sum, from chartCost relative
to the actual Aflat scalar. -/
def salted :=
    quotaCharge x A F J β Finset.univ - (1/2:ℝ)*(Real.log (Rows.gram T x V k (shots S x) A F).det-
      Real.log (LocalLog.flat T x k F).det)+shiftCharge T x V A k F C









/-- For use on the full-base extracted scalar convention, not assuming
mayer reconstruction. Keep coarse tail inside, keep v per-site outside
(see `SectorChange.full_price`). -/
def owingFull (R : Rep G f) (B : BudgetPoint) :=
    owing T x w V A O k F D p q J d m C Y z R * Real.exp (coarseTail T x B V R.beta - R.v * Fintype.card (Site f))


end YM.AnalyticBridge.Annulus
