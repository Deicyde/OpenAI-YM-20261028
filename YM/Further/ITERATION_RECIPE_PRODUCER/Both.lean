import YM.Extra.ITERATION_NO_LOSS.Local
import YM.Extra.WILSON_STARTUP.Clock
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Recipe
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Progress.JOINT_CALENDAR.Issue

set_option warningAsError false

/-!
# Running both handoffs (conditional on physical integrand estimates)

Obligations PRIOR to the E/forced attachment merger, in Rebuild's rates on
the actual physical fields.

The estimator can pay with full additional
support exponent reserves, and continuity with a different exponent.

We
keep the same threshold for the stated exact identity.

No impossibility
of negative Δ assumed.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe.Swap
open Function Filter Set Lattice Wilson RG RG.Supply RG.Shoot Precision Bid Exterior Extra.Iteration Ovens Ovens.Pipes
open Next.Scheduling Progress.DirectedRecipe Input Rebuild Comparison
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n m : Side} {s t : BudgetPoint}





variable {f : ℝ → Tap G n} {X : Pipes G n} {T : Set ℝ}



variable {S : Sheet G} {D : Rolls S} {a : Levels G} {M : Horizon a} {O : ChartRatio G} {k : Kin M O}
    {V : Rebuild.Census} {F : Rebuild.Fuel D} {e : ℕ → ℕ → Exchange} {u : ℕ → ℕ → Postage} {r : Permissions a}

/-- Stronger optional edge bill *at the assembly threshold*. Placing it in
`follows` makes it non-optional at EVERY ancestry use (so not on the old
recipe from merely exhibiting one compatible choice). -/
structure Labelled (V : Rebuild.Census) (F : Rebuild.Fuel D) (r : Permissions a) (N m p : ℕ) (Q : Rep G (a.S.side (m+1) p))
    (Δ : ℝ) (X : Pipes G (a.S.side m p)) (d : Tap G (a.S.side m p)) : Prop where
  earnings : Ingredients X d (a.budget m) (F.regular a V m Q.beta) (F.strong a m Q.beta)
  kinetic : (a.clock.threshold m)^2 * |Δ| ≤ F.total a V m Q.beta
  old : r.follows N m p Q Δ X d

def stamp (V : Rebuild.Census) (F : Rebuild.Fuel D) (r : Permissions a) : Permissions a := {r with follows := Labelled V F r}


/-- Matching raw output with possibly different reserve s. The estimator's
responsibility, including the startup-independent joint `Ingredients`
summability and symmetry tests and its predecessors' actual flags. No
pasted pointwise δ corrections after solving different normalization tests.
-/
structure Raw (k : Kin M O) (V : Rebuild.Census) (F : Rebuild.Fuel D) (r : Permissions a)
    (N m p : ℕ) (Q : Rep G (a.S.side (m+1) p)) (Δ : ℝ) (X : Pipes G (a.S.side m p)) (d : Tap G (a.S.side m p))
    (s : BudgetPoint) : Prop where
  earnings : Ingredients X d s (F.regular a V m Q.beta) (F.strong a m Q.beta)
  kinetic : (a.clock.threshold m)^2 * |Δ| ≤ F.total a V m Q.beta
  permit : r.follows N m p Q Δ X d
  splitting U : (trunk (k.path N m) (a.params m).clip s X d (Q.beta + k.alpha N m + Δ) 0).eval U * Real.exp (∑' i, d.logarithm i U) =
        (a.clock.op m p).push Q.beta Q.eval U / (a.clock.op m p).push Q.beta Q.eval 1

variable {N m p : ℕ} {s : BudgetPoint}










variable {K : MapPrices} {s₀ : Survey G} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s₀.paper q v)} {T : Protection D}
    {F : Rebuild.Fuel D} {W : Supply.Delays T} {Y : Bar W} {I : Wait Y} {B : Beam K D}


end YM.Further.IterationRecipe.Swap
