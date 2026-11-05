import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorLie
import YM.Extra.ITERATION_NO_LOSS.Kernels
import YM.Extra.MULTISOURCE_BOUNDS.Delays
import YM.Next.ROTATIONS.Dyad
import YM.Progress.STATIONARY_SCENES.Probe
import YM.Push.RELAY_DIFFERENCE.Estimate
import YM.Push.RELAY_MARK.Budget
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Campaign
import YM.UVNext.PRICED_KERNELS.Seats

/-!
# Example downstream costs for actual Gaussian quadratic multipliers

On the true `Book` Lie norm (so even when A e grows polynomially in the
separation the location powers are kept INSIDE the z-budget). This
contribution of `Rows.adjustment` keeps the ordered version of its post-L
exponential saving; never drops the factor as negligible inside the measure.
Also a marginal use, WITHOUT mistaking its inverse for an entrywise patch
of a full precision. Does not include the Jacobian/scalar/unselected/sieve
factors as part of these estimates. Not a multiplier normalization claim.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Function Filter WardBin.Lies Precision Tree
  FreeResolvent Affine Mark TestD Matrix
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c : Side} {j : ℕ} {X ι : Type*} [Fintype ι]

def probe (z : ι → ℝ) : Matrix ι ι ℝ →L[ℝ] ℝ := ({
    toFun F := dotProduct z (F *ᵥ z)
    map_add' _ _ := by rw [Matrix.add_mulVec,dotProduct_add]
    map_smul' _ _ := by rw [Matrix.smul_mulVec,dotProduct_smul]; rfl } : Matrix ι ι ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

variable {F : Config G c → Matrix ι ι ℝ} {V : Config G c} {D : Cost X} {a : Edge (Site c) → X} {o : X} {b : ι → X}












namespace Sector
open YM.Next.SectorChange YM.Pressure Rows Wisps
variable {f : Side} {S : StepData c f} {x : ℝ} {A : Stores S} {T : Forest S.ratio} {k : S.Choices} {H : Tube G S} {q : ℕ}
  {σ s M N r d Y g δ Y' fee : ℝ} {P : ℕ} {o : Site c}





variable (h : Loans H x A T k V q M d r Y δ g Y')
  (l : List (Directions G c)) (hl : l.length ≤ q) (hfee : 0 ≤ fee)
  (hB : ∀ B ∈ l, ∀ t, ‖B t‖ ≤ fee*(1+(separation t.1 o:ℝ))^P)
include h hl hfee hB



variable {ι : Type} [Fintype ι] [DecidableEq ι]


end Sector
end YM.SelectedOrderedKernels
