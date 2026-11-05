import YM.Further.CURVED_GAUSSIAN_JETS.Weights
import YM.Further.CURVED_GAUSSIAN_JETS.Windows

/-!
# Center-price and affine linear residual error in the same jets

In the Frco convention b HERE reads Dᵀ F₀. Includes derivative cost
for b and order-dependent weights at the external directions' origin.
No extensional assumption about a background outside each germ.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Jets
open Function Filter MeasureTheory Set Matrix Lattice SectorNext.Vacuum Wilson RG Precision Progress.StationaryScenes
open Green (wt)
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
open Next.Foundations (left_has)
variable {n c : Side} {G : Gauge} {I : Type*} [Fintype I] [DecidableEq I] (W : Windows I) {a : I → Site n}
    {U : Config G c} {A : Field G c I} {b : Config G c → Vec I} {s : Weights a} {r M C : ℝ} {k N : ℕ}
    {Q : Directions G c → Prop} {p : Prices}


structure Bounded (b : Config G c → Vec I) (s : Weights a) (k : ℕ) (Q : Directions G c → Prop) (U : Config G c) (C : ℝ) : Prop where
  smooth (i : I) : ContDiffAt ℝ (k:WithTop ℕ∞) (fun y => b (increment U y) i) 0
  bounds (l : Word G c) : l.length≤k → (∀ i∈l,Q i) → ∀ i, ‖leftDerivs (fun V=> b V i) l U‖ ≤ C*s.τ i^l.length








variable (b : Config G c → Vec I)
def center (A : Field G c I) (V : Config G c) := W.mean (A V) (b V)

variable {b}



end YM.Further.CurvedGaussianJets.Jets
