import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Merge
import YM.Bid.Tar
import YM.Org.Theatre
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Work.A05.Read
import YM.Work.B04


set_option warningAsError false

/-!
# Wire the first system to the log/exclusion calculation

Choose alphabet, footprints, output inventories independently of field values.
`internal` is for tests local to selections (as determined by full query
footprints, not necessarily just the previous geometry's exclusion).
Still require the component-factorization check on word integrals; don't
silently assume all points or tags or Gaussian marginals can be split.
See `Marginal` for lower level versions. Includes applications to per-spelling
prices; these are per *term*, don't ask for summability estimates on the
completed K or E. Supply them where the actual term is evaluated on V
(or as sup bounds); e.g. lots of physical work remains after `full_grant`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.FromWords
open Lattice Wilson RG AbsoluteSums AbsoluteSums.Multiple Finset Filter Function Ursell Trees  
open scoped Topology BigOperators Classical
variable {n : Side} {ι : Type*} (X I : ι → Support n)

abbrev UF := {i : Species X // owned X I i = ∅}
abbrev FC := {i : Species X // (owned X I i).Nonempty}

abbrev XY (i : FC X I) := ground X i.val
abbrev XX (i : UF X I) := ground X i.val
abbrev IS (i : FC X I) := owned X I i.val

/-- Complete integrated amplitudes at field with flag set D. Keep
all discrete tests that could have failed, even if all their V reads
are elsewhere supplied. The final flag-read check itself uses the
one-time external halo.
-/
def money (test : ι → Finset ι → Prop) (eval : Species X → ℝ) (i : Species X) :=
  if internal X test i.val then eval i else 0



def forced (D : Support n) (test : ι → Finset ι → Prop) (eval : Species X → ℝ) (i : FC X I) :=
  if XY X I i ∩ D = IS X I i then money X test eval i.val else 0

def dictionary : FC X I ⊕ UF X I ≃ Species X where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun := fun i => if h : owned X I i = ∅ then Sum.inr ⟨i,h⟩ else Sum.inl ⟨i,nonempty_iff_ne_empty.mpr h⟩
  right_inv := fun i => by dsimp only; split <;> rfl
  left_inv i := by
    rcases i with i|i
    · dsimp only [Sum.elim_inl]; rw [dif_neg i.property.ne_empty]
    dsimp only [Sum.elim_inr]; rw [dif_pos i.property]







section Wire
variable (D : Support n) (test : ι → Finset ι → Prop)
    (eval : Finset ι → ℝ) (loc : Species X → ℝ)









/-- Per-connected-spelling check (e.g. from per-letter estimates, a
*mixed* packet account, Gaussian product bounds etc). Must fit enough
additional exponent for the log (and, for subsequent K budgets, the
merger recursion). Wire every check to the SAME local evaluation loc as
derived from the component identity. -/
structure Prices (b : Species X → ℝ) : Prop where
  pos : ∀ i,0 ≤ b i
  gets : ∀ p, internal X test p.val → ground X p ∩ D = owned X I p → ‖loc p‖ ≤ b p




end Wire

section Income






end Income
end YM.Push.LogIdentity.FromWords
