import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Progress.STATIONARY_SCENES.SliceGap



set_option warningAsError false

/-!
# E station uncut flat comparator. Don't mix sector determinants and this one

Here **derive** the Schur complement (incl momenta where a transverse
inverse formula would involve zero). `metric` same retained floor; C of
`Fiber` not this automatically! These are consistency and comparison
lemmas, in all color slots and using `probe`, `link`, roots, any tree.
All finite torus of a step covered by real `trial`. We never integrate a
Gaussian on the *whole* joint matrix -- involves ungrounded coarse gauges
and harmonics. Hessian of action in **absolute** flat additive link,
y fixed while integrating (relative to a copied external coarse field,
input mean would be shifted accordingly).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar.Uncut
open Matrix Function Filter Precision  Lattice Tree RG Bid Wilson Exterior Bloch
open YM.Progress.StationaryScenes.Green
open MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable (G : Gauge) {I J T : Type*}










variable {c f : Side} {S : StepData c f} (F : Forest S.ratio)

/-- Include with zeros on trunks. No path orientation signs omitted -- this
inclusion itself is only on positive Edge. -/
def mark : Matrix (Body 1 f) F.Free ℝ := Matrix.of fun i j => if i=link F j then 1 else 0

























end YM.Further.GaussianScalar.Uncut
