import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Liouville
import YM.Progress.CLASSICAL_KIN_RECURSION.Merge
import YM.Progress.CLASSICAL_KIN_RECURSION.Pier
import YM.Progress.CLASSICAL_KIN_RECURSION.Row

set_option warningAsError false

/-!
# Path realization in exactly Atom & Budget

Address includes all relative translations, including any that wind in
an evaluation. Cost uses the *sum* of their lengths, stores one
canonical route for each. Here arity k≥1 for pack – the unit component
isn't a path correction. Arity three and four of interest here.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin
open Lattice RG Laurent Exterior Spools
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {k : ℕ} {n : Side}

abbrev Mount (k : ℕ) := ((Fin k → Finset Axis) × Shift (Fin k×Axis))

def marks (k : ℕ) [NeZero k] : ℕ ≃ Mount k := index _

def laurels (S : Finset Axis) : PlaqAxes :=
    if h : S.card=2 then plaqEquiv.symm ⟨S,h⟩ else ⟨(0,1),by decide⟩


def shelves (u : Voices (Fin k) G.ColorIndex) (a : Mount k) : Atom G k where
  leg i:=foot (laurels (a.1 i)) (shoe i a.2)
  coeff := (u a.1).val a.2














end YM.Progress.ClassicalKin
