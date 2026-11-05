import YM.Further.CURVED_GAUSSIAN_JETS.Transit
import YM.Further.CURVED_GAUSSIAN_JETS.Zones

/-!
# The jumps in the ordered expressions are short in the assigned metric

Numerical range only (same matrix, windows never omit rows).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Tracks
open Matrix Function Filter Jets Lattice Wilson RG Precision Push.Uniform SectorNext.Vacuum Set MeasureTheory
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {I J X : Type*} [Fintype I] [Fintype J] [Fintype X] [DecidableEq I] {n : Side} {a : I → Site n} {b : J → Site n} {c : X → Site n} {L M N : ℕ}

def Strip (a : I→ Site n) (b : J → Site n) (M : ℕ) (A : Matrix I J ℝ) := ∀ i j, M < separation (a i) (b j) → A i j=0
abbrev Reach (a : I → Site n) (M : ℕ) := Strip a a M
namespace Strip
variable {A A' : Matrix I J ℝ} (h : Strip a b L A)
include h







end Strip



section column
variable {A : Table I} {W : Windows I}

def Nearby (W : Windows I) (a : I → Site n) (M : ℕ) := ∀ (i j : I), j∈W.box i → separation (a i) (a j) ≤ M




end column

variable {G : Gauge} {m : Side} {A : Jets.Field G m I} {W : Windows I} (hw : Nearby W a M) (h : ∀ v, Reach a N (A v)) {d : ℕ}

include hw h



omit hw h in
lemma drop_flat {B : Fin d → Jets.Field G m I} {p : Run I d} (h : ∀ i v, Reach a N (B i v)) (hp : ¬Hops a N p) (V : Config G m) : parcel p B V=0 := by
  obtain ⟨i,hi⟩ := not_forall.mp hp
  exact Finset.prod_eq_zero (Finset.mem_univ i) (h i V _ _ (Nat.lt_of_not_ge hi))



end YM.Further.CurvedGaussianJets.Tracks
