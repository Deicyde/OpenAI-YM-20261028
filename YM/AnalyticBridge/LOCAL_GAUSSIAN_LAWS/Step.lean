import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Density
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.DensityPrice
import YM.Push.CUTOFF_PROJECTORS.Signed
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stamped


/-!
# Client theorem at a single step: either actual Gaussian

At every *fixed patch* post-L, choose the same delay for the true
Haar chart licenses and for the window comparison.

The second prescription
specified here reads the SAME Q=gram in the  midpoint windows of
FreeResolvent.

Exactly the normalized sector (Licenses) for either AND
the change-of-law for the two with the same shifts, all at the same step.

No global smallness/pricing promised; logdet cost reported with its
coordinate count (same formula also in next local comparison files).

This is a ``point of sale'' theorem that also works on Permit.tube (see
client), not an independent promise on different configs, nor does it
insert a wait into any previously issued clock.

Parsing note: x here is hatBeta COARSE, d = C*fiery from
sponsored_permit eventual; preserve that order if joining sales across
steps.

R.beta is its own actual fine β.

No need equality with x.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented Presented
open Next SectorChange SectorChange.Rows SectorChange.Gaussian Wisps
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {x : ℝ}

/-- True midpoint alternative in the *same* sector. -/
def midOrder (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) :=
  pane (midSets S (radiusB x) A F x G) (Rows.gram T x V k (shots S x) A F) 0

def midFog (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) :=
  mirror (midOrder A F T x V k)

def midLog (A : Stores S) (F : Forest S.ratio) (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
    (q : YM.Push.SectorMeasure.Chi) (d : ℝ) (y) :=
  offCenter (midOrder A F T x V k) (Rows.blame T x V k (shots S x) A F q d y)



/-- n_a is the FULL color count on active links only. Input to the shift
estimate is the actual b=D^*F0, not an uncut or differently tagged b.
Exact identities without any bound assumed on b; shift price reads ALSO
when you have a quantitative b. See `source` applications. -/
structure Ledger {w} (Pt : Teller G) (Z : ChartRatio G) (T : Tube G S) (V : Config G c) (k : S.Choices)
    (A : Stores S) (F : Forest S.ratio) (R : Rep G f) (D : Allocation G S x w) (q : YM.Push.SectorMeasure.Chi) (d : ℝ)
    (η s M C e g : ℝ) : Prop where
  stained : Admitted A F x V k Z D d
  original : Licenses T x V k A R (shots S x) F D q Z d (fog A F T x V k) (meanLog A F T x V k q d)
  switched : Licenses T x V k A R (shots S x) F D q Z d (midFog A F T x V k) (midLog A F T x V k q d)
  exactAmount :
    let c := coupling R.beta
    let L H m :=
      chartCost H c * ∫ y, (∫ z,dyed T x V k A R (shots S x) F D q Z d H m y z ∂cloud H) ∂piHaar G (Frozen A x F)
    L (fog A F T x V k) (meanLog A F T x V k q d) = L (midFog A F T x V k) (midLog A F T x V k q d)
  leaves : A.flags = RG.flags (temp x) V →
    let Q := Rows.gram T x V k (shots S x) A F
    let Y := fog A F T x V k; let U := midFog A F T x V k
    let K (W) := Closes (FreeResolvent.native _) (front A F) Q W s M η C e g
    let N : ℝ := Fintype.card (In x A F (G:=G))
    let shift (y) := (coupling R.beta)⁻¹ • (midLog A F T x V k q d y-meanLog A F T x V k q d y)
    let H (u) (y) z := dyed T x V k A R (shots S x) F D q Z d Y (meanLog A F T x V k q d) y (z+u)
    Permitted x V k A F D Z d R.beta Y (meanLog A F T x V k q d) ∧
      Permitted x V k A F D Z d R.beta U (midLog A F T x V k q d) ∧
      (∃ B, 0 < B ∧ Authorized A V F x B) ∧ K (panels A F) ∧ K (midSets S (radiusB x) A F x G) ∧
    ∀ y z, Density.replace Y U (shift y) z * H (shift y) y z = Density.chip Y U * dyed T x V k A R (shots S x) F D q Z d U (midLog A F T x V k q d) y z ∧
      ∀ t : ℝ, 0 ≤ t → (∀ i, |Rows.blame T x V k (shots S x) A F q d y i| ≤ t) →
        |Real.log (Density.replace Y U (shift y) z)| ≤ e*((2*M^2+M)*(z ⬝ᵥ z)+2*M*N*(1+(2*t/coupling R.beta)^2))


end YM.AnalyticBridge.LocalGaussianLaws
