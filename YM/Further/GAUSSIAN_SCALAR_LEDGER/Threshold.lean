import YM.Further.GAUSSIAN_SCALAR_LEDGER.Rates

set_option warningAsError false

/-!
# Numeric covariance and payment of tails in the mean

Only needs bounds on precision and the geometry of *these* windows,
no assumptions of positivity or determinant lower bound on cropped
covariance. The delay below is only numerical, not physical funding.
Gets uniformity over ALL all such `RawPrice` and windows (pay fixed-L).
Value order (field derivatives and stencils of rows not purchased).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function Filter Precision SectorNext.Vacuum Lattice
open Round (rowRate)
open YM.Progress.StationaryScenes.Green
open scoped Topology BigOperators Matrix.Norms.Frobenius

structure Timing (p : Expense) (r : ℝ) : Prop where
  misses : p.windowCost r < 1/2
  small : p.correctionCost r < 1/2

lemma Expense.delayed (p : Expense) : ∀ᶠ r : ℝ in atTop, Timing p r := by
  filter_upwards [p.ages.eventually (gt_mem_nhds (show (0:ℝ)< 1/2 by norm_num)),
    p.pays.eventually (gt_mem_nhds (show (0:ℝ)< 1/2 by norm_num))] with r he hb
  exact ⟨hb,he⟩

namespace RawPrice

variable {c : Side} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Z : Lens ι) (p : Expense) {y : ι → Site c} {A : Wall ι} (h : RawPrice p y A)
include h



-- Permit also smallness just of correctionCost (#p drift).






omit h in
def meanAt (Z : Lens ι) (A : Wall ι) (b : VV ι) := -(Z.visit A 0)ᵀ *ᵥ b


end RawPrice
end YM.Further.GaussianScalar
