import YM.Further.CURVED_GAUSSIAN_JETS.Windows
import YM.Progress.STATIONARY_SCENES.SliceGap


/-!
# Flat ledger before the sector deformation (written in the correct keys)

With tree invariance and the **relative** log prices. See Signed/ShortGap
for cut conventions. Use these particular cut numbers e.g. together with
explicit identification in Stamped on the sectors, not as a claim about an
unspecified change-of-variables producer.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Tint
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Wilson Tree RG Precision Work
open Progress.StationaryScenes Bid Exterior Bloch Pressure  FlatTree
open Green (wt link)
open Rows (Bill)
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical Kronecker
variable {c f n : Side} {S : StepData c f} (F H : Forest S.ratio) {G : Gauge}
variable (J : Type*) [DecidableEq J] [Fintype J]
variable {I X Y : Type*} [DecidableEq I] [Fintype I] [Fintype X] [Fintype Y]

def row (A : Matrix I X ℝ) : Matrix (I×J) (X×J) ℝ := A ⊗ₖ (1:Table J)
lemma row_apply (A : Matrix I X ℝ) (i : I × J) (j : X×J) : row J A i j = if i.2=j.2 then A i.1 j.1 else 0 := by rw [row,kronecker_one, blockDiagonal_apply]
lemma product (A : Matrix I X ℝ) (B : Matrix X Y ℝ) : row J (A*B) = row J A * row J B := by rw [row,row,row,← mul_kronecker_mul,mul_one]
lemma transpose (A : Matrix I X ℝ) : row J A.transpose = (row J A).transpose := by rw [row,row,← kroneckerMap_transpose, transpose_one]




lemma cash (A : Table I) (x y : Vec (I×J)) : dotProduct x (row J A *ᵥ y) = ∑ j : J, dotProduct (fun i => x (i,j)) (A *ᵥ (fun i => y (i,j))) := by
  simp only [mulVec,dotProduct,row_apply, ite_mul, zero_mul,Fintype.sum_prod_type]; rw [Finset.sum_comm]; simp

def next (p : Prices) : Prices := { p with tags := p.tags * Fintype.card J }







end YM.Further.CurvedGaussianJets.Tint
