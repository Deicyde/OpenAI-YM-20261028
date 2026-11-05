import YM.Next.BOUNDARY.Descends
import YM.Next.UV_STRESS.Tensor
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Current
import YM.Work.A09
import YM.Work.A12

/-!
# Reduce what's requested on the free side of RGrades too

NOT addressing here the Maxwell/free-hierarchy production problem.
Eliminate obligations from MaxwellData/Freediv that follow from its other
obligations by the *accepted* results. Don't assume arbitrary Ranks
comparison or pay for Noether normalization twice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Spec Lattice Wilson Cells
  Next.Extract Next.UVStress Work.A01
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G}

/-- Demands at the free comparator after Lorentz + polynomial results.
T still on the **actual Bel** of C. Lighthouse κ nonzero is enforced
on T. lit keeps the unnormalized StressLaws via that same κ incl ν
term. Also needs full frame/detector preparation. -/
structure FreeInput (C : Family G) where
  T : Lighthouse C.book
  kernels : (Bel C.book).Hierarchy
  lit : T.Goes C.book kernels.spin
  internalTest : erases kernels.spin T.W

namespace FreeInput
/-- Not from sale of spectral rank alone. Lie from Port, then Casimir and
marks from !A bids; Lorentz Spins from Euclidean rotation laws. -/
def reads (p : FreeInput C) : MaxwellData C where
  T := p.T
  hT := p.kernels
  lit := p.lit
  vacuum := Classical.choose (Next.BOUNDARY.spins_producer p.kernels.laws.toSymmetric p.lit.edges p.lit.turns).exists
  rolls := Classical.choose_spec (Next.BOUNDARY.spins_producer p.kernels.laws.toSymmetric p.lit.edges p.lit.turns).exists
  optic := (Work.A09.answer _ (Work.A10.answer _ _ (Next.BOUNDARY.Descent.rotation_port p.T.K p.lit.turns)).1).1
  marks := Work.A12.answer _ _ (Next.BOUNDARY.Descent.rotation_port p.T.K p.lit.turns)
  frames := p.internalTest

theorem reads_spin_eq (p : MaxwellData C) : reads ⟨p.T,p.hT,p.lit,p.frames⟩=p := by
  cases p with
  | mk T a lit k hk R Y I =>
    have he := Next.BOUNDARY.spins_producer a.laws.toSymmetric lit.edges lit.turns
    have hp : Classical.choose he.exists=k := he.unique (Classical.choose_spec he.exists) hk
    subst k; rfl



/-- Only these additional Maxwell `FreeDiv` receipts. Symmetric and
real included in enters, sign from lit itself on the genuine hierarchy.
(Not solving the key Maxwell precursor here.) -/
structure Divergence (p : FreeInput C) : Prop where
  reached : Surjective (currentDiv p.T.W p.kernels.spin p.lit.hers)
  line : Module.finrank ℝ (LinearMap.ker (currentDiv p.T.W p.kernels.spin p.lit.hers))=1
  enters : p.T.J ∈ KernelSpace p.kernels.spin
  balance (i : Axis) : ∑ a, p.T.W.deriv 4 a (p.T.J a i)=0


end FreeInput
end YM.UVNext.Grade
