import YM.Next.SCHEDULE.Dues
import YM.Progress.DIRECTED_RECIPE.Motion


/-!
At a given step/period, on input-Q Curves. When trying to prove the raw
per-address estimates in a parameter neighborhood, the operator may need not
only to know the input E jets at fixed sites vary in β, but may use them at
MOVING fields with moving directions. Need their actual joint continuity.
Here prove it within the paid health/direction domain. Work with the given
unmasked extension, no assumptions on tests away from it; even at points
of threshold equality. Includes *all* ordered left derivatives. Does not give
joint continuity of `K` in field! Those must be held separately. See .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe
open Function Set RG Wilson Lattice RG.Shoot MeasureTheory Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n : Side}

section jets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- The change chart lemma in Foundations handles the fixed l derivative
-- internally. Here need the extra moving variables *during* the smoothness
-- proof; use recentering with them. Public plog/diff apply on any G.

lemma shifted {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {x : D} {u v : D → Directions G n} {m : WithTop ℕ∞} (h : u x=0) (hh : v x=0)
    (he : ContDiffAt ℝ m u x) (hf : ContDiffAt ℝ m v x) :
    ∃ k : D → Directions G n, k x=0 ∧ ContDiffAt ℝ m k x ∧ ∀ U,
      (fun y => increment (increment U (u y)) (v y)) =ᶠ[𝓝 x] fun y => increment U (k y) := by
  let a (y : D) (i : Edge (Site n)) := G.lieExp ((v y) i) * G.lieExp ((u y) i)
  have hk i : a x i=1 := by simp only [a,hh,h,Pi.zero_apply,G.mat_lieExp_zero,mul_one]
  let k y i := G.plog (G.mat (a y i))
  have hb i : Tendsto (fun y => a y i) (𝓝 x) (𝓝 1) := by
    rw [← hk i]; apply ContinuousAt.tendsto
    exact (G.lieExp_cont.continuousAt.comp ((continuous_apply i).continuousAt.comp hf.continuousAt)).mul
      (G.lieExp_cont.continuousAt.comp ((continuous_apply i).continuousAt.comp he.continuousAt))
  refine ⟨k,funext fun i => ?_,contDiffAt_pi.mpr fun i => ?_,?_⟩
  · simp [k,hk]
  · have hg : ContDiffAt ℝ m G.plog (G.mat (a x i)) := by
      rw [hk,G.mat_one]; exact G.plog_diff.of_le le_top
    refine hg.comp (f:=fun y => G.mat (a y i)) x ?_
    simp only [a,G.mat_mul]; apply ContDiffAt.mul
    · exact ((G.exp_jet.of_le le_top).contDiffAt).comp _ ((contDiffAt_apply _ _ _ _).comp x hf)
    exact ((G.exp_jet.of_le le_top).contDiffAt).comp _ ((contDiffAt_apply _ _ _ _).comp x he)
  intro U
  filter_upwards [eventually_all.mpr fun i => (hb i).eventually G.plog_right] with y hy
  funext i
  rw [increment,increment,increment, ← mul_assoc]; rw [show G.lieExp (k y i)=_ from hy i]








end jets












end YM.Progress.DirectedRecipe
