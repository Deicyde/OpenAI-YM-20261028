import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Anchored
import YM.Push.FREE_RESOLVENT.Differentiated


/-!
# Prices with positive marks

Same rate on pairs and on each external Taylor position, anchored
independently at each output slot. Fixed-point `ContDiffAt` (ordinary
real chart jets), no arbitrary chart transition. Include adapters needed for
buying products at a slightly smaller rate, and applying to radial tests
about an external coarse site.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Function Filter Lattice RG Wilson Pressure Precision Tree
open Next.SectorChange 
open FreeResolvent Mark TestD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side}
variable {α β : Type} [Fintype α] [Fintype β]

/-- Absolute costs through n with actual occurrence marks (B70
coordinates, no one-sided derivatives). See `Mark.Bill`. -/
abbrev Tagged (p : α → Site c) (q : β → Site c) (n : ℕ) (t M : ℝ)
    (A : Coord G c → Matrix α β ℝ) (x : Coord G c) :=
  Bundle (direction G c) (locations G c t) (native c) p q A x n t M

variable {p : α → Site c} {q : β → Site c} {s t u C D : ℝ} {l : List (Index G c)}

lemma marks_decrease (hs : t ≤ s) (o : Site c) :
    (locations G c t).pay l o ≤ (locations G c s).pay l o := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih =>
    rw [Mark.pay,Mark.pay]
    exact mul_le_mul ((native c).weight_mono hs o (root a)) ih (pay_pos ..).le (Mark.pos ..).le

omit [Fintype α] in
lemma rate_budget {M : Matrix α β ℝ} (H : Mark.Rates (locations G c s) (native c) p q l u C M)
    (hs : t ≤ s) : Mark.Rates (locations G c t) (native c) p q l u C M := by
  constructor; intro i; refine le_trans ?_ (H.rows i)
  exact mul_le_mul_of_nonneg_right (marks_decrease hs _) (Finset.sum_nonneg fun j _ =>
    mul_nonneg ((native c).weight_nn ..) (abs_nonneg _))

lemma marks_budget {M : Matrix α β ℝ} (H : Bill (locations G c s) (native c) p q l u C M)
    (hs : t ≤ s) : Bill (locations G c t) (native c) p q l u C M :=
  ⟨rate_budget H.row hs,rate_budget H.col hs⟩

namespace Tagged
variable {n k : ℕ} {A : Coord G c → Matrix α β ℝ} {x : Coord G c}






lemma order_zero (h : Tagged p q n s C A x) : (native c).Schur p q s C (A x) := by
  simpa only [zeroth] using Bill.reclaim (h.bound [] (Nat.zero_le n))


end Tagged






end YM.AnalyticBridge.NonflatCovarianceLocality
