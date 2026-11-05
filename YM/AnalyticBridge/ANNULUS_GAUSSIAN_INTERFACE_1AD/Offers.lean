import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Count
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Earn
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Void
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.WindowLog
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Contraction
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ledger




/-!
#  dictionary entry and precise unpriced companions

Zero order real variables. Fix V (all evaluations in that branch/frame,
including mean), one A and F, and use the genuine colored counting z,
post-chart variables exactly as in Change. Reserve *all* selected
profiles through the displayed locations. D defaults in the *rest*
of the formula are still there (expanding them comes later). K factors
and their eligibility always kept explicitly. No differentiation of
flags; no assuming dictionary functions can be evaluated if varying
the held data of different components independently.
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Affine Finset

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Tube G S) (V : Config G c) (x : ℝ) (A O : Stores S) (k : S.Choices) (F : Forest S.ratio) (q : Chi)
variable (R : Rep G f) (w d : ℝ) (H : ChartRatio G) (qS : Chi) -- seed profile qS, broad q.
variable (Y : LinkArray G (Frozen A x F))

/-- Local regular Haar cost (separate from all scale factors). -/
def capsule (X : Finset (Active A x F)) (a : LogArray G (Active A x F)) :=
  (∏ i∈X, extended q H d (a i))*(∏ i∈X,broad q d (a i))



lemma capsule_le (X : Finset (Active A x F)) (a : LogArray G (Active A x F)) (h : LocalRatio H)
    (hd : 0<d) (hr : 4*d < H.radius) : capsule x A F q d H X a∈Set.Icc (0:ℝ) 1 :=
  unit_product
    (unit_alphabet _ _ fun _ _ => ⟨(gentle_extended h q hd hr _).1.le,(gentle_extended h q hd hr _).2⟩)
    (unit_alphabet _ _ fun _ _ => broad_range q _ _)

def grab (C : Finset (Frozen A x F)) := -(C.card : ℝ) * Real.log (spare H R.beta)



variable (D : ℕ) -- radiusB multiple for kernel, profiles through D+100, broad through D+104
variable (L : ℝ) -- paired precision common scale
variable (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
variable (b : Finset ℕ)

/-- *one* compulsory packet factor. Compare:

* item 1 exactly cut drows minus selected + the matching first
Frco on same rows of (now translated) cutoff mean m, even
when m depends on Y. Located by anchorage in `Stores` convention
(up to D). Plus one local paired log per canonical fine bond
(both endpoints in the sense *test* both, i.e. min distance); not
price full determinant this way. The rest of log goes to the companion.
* item 2 frozen deficits from exact Fsct (no global factor
estimated to continue extraction); take also the separated reference
likelihood in the probabilities of the kernel, not summing over k.
Repaying the tag factor to probability-reference expectation
(counting cardinality) can be done when consuming. We retain actual
likelihoods even in the larger collar (and exact rest), no asserting
that *turned Q noise equals unturned Q noise under the same rotation as
v* for paying squared terms.
* item 3 actual profile partitions and agreement (including actual
output flags), all default factors through D+100. True q factors
per fine site, still read *original* K supports for deciding use.
K factors themselves outside the exponent and these offers; to be
paid separately even if the incidence test then forces into packet later.
* item 4 regular broad charts and *their ratios*, per active link
through D+104. Preserve their data (and outside them preserve the
corresponding data of the companion). Keeping qS vs q separate
also permits driving the general guard chi in the E prescription.

Supports intended for payment and tests as in E. Not a claim of
reconnection into *functions only of* the coordinates on these
positions: e.g. m may read elsewhere, path decisions for v may read
other tags. Use with authentic A, T, F, V, Theta and U=landed here;
later recipes still need cover, localization and covariance costs
for every such read. -/
def offer (z : Prices G (Active A x F)) :=
  let B := radiusB x; let N := O.dome ((D+100)*B)
  let a := m Y + coupling R.beta • z
  let U := landed x A F V Y a
  let M s := anchorage (turnStore s O) (D*B)
  receipts qS A x w N (nearFace S N) (nearNoise N) U V k *
    capsule x A F q d H (locals A O x F ((D+104)*B)) (tape a) * voids R.activities R.p U b (covered N S) *
    Real.exp (emission T V x A k F q d Y M R.beta (m Y) z + (∑ i∈everyLink S O (D*B), couple T V x k A F L i)+
      grab x A F R H (driftwood A O x F))







end YM.AnalyticBridge.Annulus1AD
