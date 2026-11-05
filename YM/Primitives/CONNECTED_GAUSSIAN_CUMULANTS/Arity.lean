import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Price

/-!
# One finite-arity uniform roughening

Alternative to keeping a whole list of tree geometry values. Retain tree
length `extent`, not a factorial hidden in `Θ`. No promise that paying
this arity overhead is sensible when the number of labels goes unbounded.
The valence test also permits SMALL leg weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory Function Finset Marker
open YM.Multi.Vacuum.Gauss Probe Grove Fused Moment Expansion Charge Connector Lattice Price
open YM.Next.SectorChange.Schur YM.Next.SectorChange.Wisps YM.Extra.Trajectories
open scoped Topology BigOperators
variable {V I J : Type} [DecidableEq V]
namespace Arity





section trees
variable [Fintype V]


end trees

section price
variable {n : Side} (X : V → Support n) (S : V → Finset I)

def extent (T : Finset V) (o : V) (f : Parent V) := ∑ i∈T\{o}, gap (X (f i)) (X i)





omit [DecidableEq V] in
lemma border_nn {α μ K : ℝ} (hK : 0 ≤ K) (i j : V) : 0 ≤ border S X α μ K i j := by
  unfold border rate cents; dsimp only; positivity



variable [Fintype I] [Fintype J] [DecidableEq I] [Fintype V] {q : Rows V I J}
-- expose precisely the cost independent of copy count away from chosen T




end price
end Arity
end YM.Primitives.GCC
