import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.LogAction
import YM.Bid.Fuels
import YM.Work.A05.Read
import YM.Work.A07

set_option warningAsError false

/-!
# Relabeling entire histories in the log/exclusion merger

This charges no prices and assumes no H action on derivative frames; for
Moves consume exact transformations of the integrated label alphabet
itself. Gauge/smoothness separately. Formulate with `Finset.map` here
(to also use e.g. on a sum type with arbitrary decidability) and adapt
to image with actual Signed later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Rename
open Lattice RG Wilson Finset Filter Function Relation
open  Restore  AbsoluteSums AbsoluteSums.Ursell Attach
open scoped Topology BigOperators Classical

variable {ι κ : Type*}

def send (e : Equiv.Perm ι) := e.finsetCongr

lemma listed (e : Equiv.Perm ι) (i : ι) (s : Finset ι) : e i ∈ send e s ↔ i∈s := by simp [send,Equiv.finsetCongr]
lemma through [DecidableEq ι] (e : Equiv.Perm ι) (s : Finset ι) : send e s = s.image e := Finset.map_eq_image ..
variable {n : Side}















/-- Tuple transformation. Don't permute the occurrences; keep root & factorial. -/
def tuple (e : Equiv.Perm ι) : Equiv.Perm (Clusters ι) := Equiv.sigmaCongrRight fun _ => Equiv.arrowCongr (.refl _) e

lemma tuple_area (X : ι → Support n) (a : Equiv.Perm (Site n)) (e : Equiv.Perm ι) (h : ∀ i,X (e i)=send a (X i))
    (i : Clusters ι) : Z X (tuple e i)=send a (Z X i) := by
  ext v; obtain ⟨v,rfl⟩ := a.surjective v
  rw [listed]
  simp only [Z,unionOf,mem_biUnion,mem_univ,true_and,comp_apply]
  change (∃ j : Option (Fin i.1), a v ∈ X (e (i.2 j))) ↔ _; simp_rw [h,listed]





open Multiple














end YM.Push.LogIdentity.Rename
