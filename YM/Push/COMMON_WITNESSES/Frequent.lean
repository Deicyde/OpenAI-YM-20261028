import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Fuels
import YM.Org.Theatre
import YM.Pressure.Seeds
import YM.Work.A07


/-!
# Finding a common order from *finite* numerical port checks

Can sometimes buy the financial provenance requested (esp. in Grill/Rank)
by proving only finite satisfiability of invoices at actual cutoffs BEFORE
any order is given. Beware: on a two-stage extraction this can fail, even
when each finite batch of invoices is already satisfied on some order,
unless there is some compatibility. Give an exact useful correction.
Only for countable estimate ports; e.g., make this useful for Grill via the
finite label-basis work, NOT by enumerating all real-valued tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common

open Extraction Set Function Filter 
variable {I J : Type}  
variable (f : Order) (A : I → ℕ → ℕ → Prop) (B : J → ℕ → ℕ → Prop)

/-- A and B are estimates on actual N,p. A wanted at EVERY period (even
periods outside selected range!), on one mesh sequence. B in `late` only. -/
structure OrderedTabs : Prop where
  fixed (i : I) (p : ℕ) : ∀ᶠ j : ℕ in atTop, A i (f.mesh j) p
  later (j : J) : f.late (B j)

/-- Financial input. `pay` interpreted actual N test. B need eventually
only on a cofinal allowed region o of actual periods, with horizon for each
invoice chosen before finite batches. The mesh need only cover arbitrarily
late cutoffs for each finite batch. -/
def debits (o : Set ℕ) (s : J → ℕ) (r : (I ⊕ J) × ℕ) (N : ℕ) : Prop :=
    Sum.elim (fun i => A i N r.2) (fun j => r.2 ∈ o → s j ≤ r.2 → B j N r.2) r.1

/-- Compatibility here only asked on actual finite bills (no asking
*Orders* satisfying them). Proving `.burst` in a physical calculation may
well use stronger eventual estimates once all its data are paid in C.
Need one cofinal scheme toward all future invoices! The thresholds in `s`
are period LABEL cutoffs, not physical radius. No mesh threshold across
periods in the formal input. -/
structure Bursts (o : Set ℕ) (s : J → ℕ) : Prop where
  along k : ∃ j ≥ k, f.per j∈o
  burst (r : Finset ((I ⊕ J) × ℕ)) (k : ℕ) : ∃ i ≥ k, ∀ u ∈ r, debits A B o s u (f.mesh i)

variable {f A B}



-- Assemble strict sequence by always buying from the remaining cofinal
-- reserve. Include first index (all estimates still tested eventually).


  -- nat lt





/-!
Obstruction example, about Orders (not claiming a counterexample to any
YM estimate). A batch property on ordered late estimates alone where *every
finite list* already enjoys the estimates along some order below f, but no
actual joint order possible. Explains compatibility in supplies even when the
physical estimate targets have only a `late` scope. So the previous lemmas
are important rather than just postulating that intersecting cofinal orders
would work.
-/
private def code (i : ℕ) := (Nat.unpair i).1




end YM.Push.Common
