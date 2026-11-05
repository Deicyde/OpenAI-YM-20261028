import Mathlib.Data.Set.Finite.List
import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Chart
import YM.Push.FREE_RESOLVENT.Polar
import YM.Push.FREE_RESOLVENT.Torus

/-!
# Price derivatives from active columns with two roots

Use `Index G c`: ALL actual V components. Mark every occurrence, as needed
for later finite-order charges when testing with long directions. In the D
terms the underlying radius for a short slot function may grow even at
fixed step shape. No constant cost per-slot until the true length exponential
payment has been made.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Function Lattice RG Pressure Precision Wilson Tree 
open Next.Fluctuations Next.SectorChange
open FreeResolvent Mark TestD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side}

abbrev direction (G : Gauge) (c : Side) (i : Index G c) : Coord G c := Pi.single i 1
abbrev locations (G : Gauge) (c : Side) (d : ℝ) : Mark (Index G c) (Site c) :=
  positions (native c) root d

section pay
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

structure Ends (o p : Site c) (v : Coord G c → E) (x : Coord G c) (n : ℕ) (d σ C : ℝ) : Prop where
  germ : ContDiffAt ℝ ω v x
  paid (r : Site c) : r=o ∨ r=p → ∀ l : List (Index G c), l.length ≤ n →
    (locations G c d).pay l r * ((native c).weight σ o p * ‖jet (direction G c) v l x‖) ≤ C




variable {v g : Coord G c → E} {x : Coord G c} {n R : ℕ} {d σ C D : ℝ} {o p : Site c}



namespace Ends


lemma scale (h : Ends o p v x n d σ C) (t : ℝ) : Ends o p (fun x => t • v x) x n d σ (|t| * C) := by
  refine ⟨h.germ.const_smul t,?_⟩
  intro r hr l hl
  rw [show jet (direction G c) (fun x => t • v x) l x = t • jet (direction G c) v l x from
    jet_linear (direction G c) l (A:=v) (t • ContinuousLinearMap.id ℝ E) (h.germ.of_le le_top)]
  rw [norm_smul,Real.norm_eq_abs, mul_left_comm ((native c).weight _ _ _) |t|,mul_left_comm _ |t|]
  exact mul_le_mul_of_nonneg_left (h.paid r hr l hl) (abs_nonneg _)






end Ends
end pay

variable {S : StepData c f} {z : Coord G c} {V : Config G c} {n : ℕ}
    {x : ℝ} {a : Directions G f} {i : Bond f} {u C d σ : ℝ}







end YM.AnalyticBridge.NonflatCovarianceLocality
