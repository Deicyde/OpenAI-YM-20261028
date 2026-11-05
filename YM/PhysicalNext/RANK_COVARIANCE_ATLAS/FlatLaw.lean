import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Dollars
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Selection
import YM.Next.RANK.Ratios
import YM.Push.FREE_RESOLVENT.Costed
import YM.Push.FREE_RESOLVENT.Test
import YM.Push.GRID_APPROXIMATION.AttachDefs



/-!
# Normalized flat law used for comparison

Consumer of the identity interface. Actual measure on independent REAL
color axes; show its curvature second moment on all k-slice faces is the
comparison kernel. This is *not* an `Ignition`: estimates to this law, and
fitting paths/costs and translating them jointly with the masks and fields on
the true threshold, remain serious open work. This certifies the REFERENCE
kernel used by an `hReach` estimate; not making any estimate about the
probabilities of good-set events or W production.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision Next.Free RG FreeResolvent Tree Bid
open Next.Rank Next.Rank.Atlas Next.Rank.Tapes
open MeasureTheory 
open scoped Topology BigOperators ComplexConjugate Matrix.Norms.Frobenius ContDiff ENNReal NNReal

variable {G : Gauge} {n : Side}



section moments

end moments

section density
variable {A : Levels G} {H : Horizon A} {Z : MapPrices} {l : ℕ → ℕ → ℝ} {N i p : ℕ}
variable (hH : H.Suffices Z) (hi : i<N) (F : Forest (A.clock.op i p).ratio)
variable (hs : Larger (A.clock.op i p) (G:=G))

local notation "S" => A.clock.op i p
local notation "W" => H.H N (i+1)
local notation "L" => A.S.side (i+1) p







include hH hi hs


-- Algebraic calibration of these normalized fields: physical parameters
-- `changeβ>0`, `g=anneals`. The covariance statement doesn't need values
-- of β at other levels. Jacobian/densities of real path integral not replaced.
omit hH hi hs in
lemma normal_cost (b : ℝ) (hb : 0<b) (M : Matrix (Active G F) (Active G F) ℝ) (x : Active G F→ℝ) :
    let g := (Real.sqrt b)⁻¹
    b*dotProduct (g • x) (M*ᵥ(g • x)) / 2 = dotProduct x (M*ᵥx) / 2 := by
  intro g; rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, g]; have ht:= Real.sq_sqrt hb.le; field_simp; simp [ht]

lemma actual_metric (R : PathData G) (tag : (A.clock.op i p).Choices) {c d u : ℝ}
    (hc : Sworn W L G) (ht : R.Bounds (A.params (i+1)).clip c d u) (hp : Attached W R) :
    let p := (A.params (i+1)).clip
    Precision.hessian F tag p R 0 0=treeMatrix G S F (H.H N (i+1)).metric ∧
      Affine.primary S F tag p R (fun _ => true) 0=treeMatrix G S F (H.H N (i+1)).metric := by
  intro B
  have he := hH.all N (i+1) hi L
  obtain ⟨hr,h⟩ := Work.F03.answer G _ _ S hs F W _ R c d u _ _ he ht hp hc
    (Work.F02.answer G _ R c d u ht)
  exact ⟨Tests.checked_loop F W tag _ _ hr h, Affine.identifies S F tag hs.1 ht hp he.roots hc⟩




end density
end YM.PhysicalNext.RankCovariance
