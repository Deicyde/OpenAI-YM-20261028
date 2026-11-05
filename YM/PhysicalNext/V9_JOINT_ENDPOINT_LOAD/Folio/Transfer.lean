import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Completed
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Position

/-!
# Partial actual Invoice: E's hits costed ALSO on the registered projection of affine/ratio dependencies

Pay the Part appearing in a physical derivation at locally correct flags.
V-jet transfer uses equality on fixed-table operands for all field moves;
actual value agrees even for the shifted-mean good extension under tests.
Doesn't mean a complete moving law associated to a reading is the genuine
extension at a completion (callers must agree as specified for every *used*
jet, prove off-chart participation, and e.g. cannot assume equality with
an off-flag exponential through its expectation). `Bulletin` is one price,
earned before the term or period selection. Coordinates are never colored
under another precision during an application. $Σ$ over physical labels
charges a single alphabet of potentials, no random sum per independent
sector reading it.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Matching
open AnalyticBridge.NonflatCovarianceLocality.Placement
open AnalyticBridge.LocalGaussian Further.GaussianScalar
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {I J : Type} {c f : Side} {G : Gauge} {S : StepData c f} {T : Tube G S} {P : Teller G} {x : ℝ} {A B : Stores S} {F H : Forest S.ratio} {κ : S.Choices}
    {o : Site c} {r : ℕ} {X : Support c} {p : Paper f} {V W : Config G c} {q : Chi} {d g : ℝ} {v : Charges} {k : ℕ} {bp : BudgetPoint}

abbrev Seen (x : ℝ) (A : Stores S) (F : Forest S.ratio) (V : Config G c) (i : Active A x F) := Printed x A V (site i) (settleR x)

def amount {D : Side} (p : I→Site D) (o : Site D) (s : ℕ) : (n : ℕ) → I → (Fin n → I) → ℝ
  | 0,i,_ => grade s o (p i)
  | n+1,i,h => grade s o (p i)+amount p o s n (h 0) (Fin.tail h)

lemma same_cost (n : ℕ) (i : Active A x F) (f : Fin n → Active A x F) : stretch o k n i f=amount site o k n i f := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => rw [stretch,amount,ih]





variable (b : Bulletin x P T)
namespace Bulletin
include b
private def reader (b : Bulletin x P T) (i : Active A x F) (h : Seen x A F V i) : Active (amended x A V) x F :=
  ((fields ..).mp (b.relay h i (by simp [site]))).choose
lemma reader_bond (i : Active A x F) (h : Seen x A F V i) : (b.reader i h).val.val=i.val.val :=
  Eq.symm ((fields ..).mp (b.relay h i (by simp))).choose_spec




end Bulletin
end YM.PhysicalNext.JointLoad.Folio
