import Mathlib
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Dues
import YM.Next.UV_STRESS.Across
import YM.Push.ABSOLUTE_SUMS.Basic
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Equations


/-!
# Some payments on the same addresses on both sides of a comparison

No evaluation on a selected favorable torus, or quotient of the addresses. This uses the same
charged support even on numerical zeroes.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RecursiveSecants079
open Lattice RG Wilson Push.AbsoluteSums
open scoped Matrix.Norms.Frobenius ContDiff BigOperators Classical Topology

variable {ι J : Type*} {n : Side}

namespace BothSides
variable {X : ι → Support n} {u v : ι → ℝ} {m : ℕ} {a b c d t : ℝ}

lemma hit_plus (h : Ac.Hit X m u a b) (he : Ac.Hit X m v a c) :
    Ac.Hit X m (fun i => u i + v i) a (b+c) := by
  intro x
  convert budget_plus (h x) (he x) using 1
  ext i; split <;> ring



/-- A single label is bounded by a hit price only with the nonempty-support condition. -/
lemma hit_one (h : Ac.Hit X m u a b) (ha : 0 ≤ a) (hu : ∀ i, 0 ≤ u i) (i : ι)
    (hne : (X i).Nonempty) : u i ≤ b := by
  obtain ⟨x,hX⟩ := hne
  refine le_trans (le_mul_of_one_le_right (hu i) (Real.one_le_exp
    (mul_nonneg ha (Nat.cast_nonneg (coverNumber m (X i)))))) ?_
  simpa only [hX, ↓reduceIte] using budget_single (h x) i


end BothSides



end YM.PhysicalNext.RecursiveSecants079
