import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Fares
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Registration
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Transfer

/-!
# Acknowledgements through the entire color coefficient (real ratio exponents)

One anchor can even be moved throughout the charged footprint before this
particular weight is used.

V jet at **fixed Z in the given physical
trivialization**, not moving or orthogonally rotating held prints here.

Quantitative poses with moving coordinates in Parlour.

Inputs about the
local output bits all in `Known`, not assuming every formal evaluated table
is actually eligible; extension equation for these Part reads proved only for
them.

No Hessian comparator claim or extension
of Frco's leading scalar term.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix Finset
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Matching
open AnalyticBridge.NonflatCovarianceLocality.Placement AnalyticBridge.NonflatCovarianceLocality.Full
open AnalyticBridge.SectorAffine AnalyticBridge.LocalGaussian Further.GaussianScalar
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {I : Type} {c f : Side} {G : Gauge} {S : StepData c f} {T : Tube G S} {P : Teller G} {x : ℝ} {A : Stores S} {F : Forest S.ratio} {κ : S.Choices}
    {o : Site c} {r : ℕ} {p : Paper f} {V W : Config G c} {q : Chi} {d g : ℝ} {v : Charges} {k : ℕ} {bp : BudgetPoint}







lemma amount_cost (pos : I→Site c) {n D q : ℕ} (i : I) (h : Fin n→I)
    (he : separation (pos i) o ≤ D) (ht : ∀ k,separation (pos (h k)) o ≤ D) :
    amount pos o q n i h ≤ (n+1:ℝ)*(1+D:ℝ)^q := by
  have hh (i : I) (he : separation (pos i) o ≤ D) : grade q o (pos i) ≤ (1+D:ℝ)^q := by unfold grade; gcongr
  induction n generalizing i with
  | zero => simpa only [amount,Nat.cast_zero,zero_add,one_mul] using hh i he
  | succ n ih =>
    unfold amount; push_cast
    exact (add_le_add (hh i he) (ih (h 0) (Fin.tail h) (ht 0) (fun k=>ht k.succ))).trans_eq (by ring)


namespace PartUsage
variable {ok : Active A x F→Prop} (hV : Part ok v d T κ V bp k q g)
include hV

end PartUsage

lemma known_upwards {u : Full (Active A x F)} (h : Known x A V (upwards A F x u)) {i} (hi : i ∈ clues u) : Seen x A F V i := by
  apply h (castEdge A F x i)
  simp only [upwards, preorder, Finset.mem_image]; exact ⟨i,hi,rfl⟩

namespace Bulletin
variable (b : Bulletin x P T) (hV : Value v x d T (amended x A V) F κ V bp k q g)
include b hV

end Bulletin

def candles (bp : BudgetPoint) (k : ℕ) := (bp.power*k+1)*k
def flame (v : Charges) (G : Gauge) (S : StepData c f) (r : ℕ) (x : ℝ) (bp : BudgetPoint) (k : ℕ) (p : Paper f) :=
  (2^candles bp k * premiums v G x (home S) (candles bp k) r p)^2

end YM.PhysicalNext.JointLoad.Folio
