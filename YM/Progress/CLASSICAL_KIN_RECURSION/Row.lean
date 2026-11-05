import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.PCalc.Band

set_option warningAsError false

/-!
# Real path row on the cover (for classical iteration)

A single choice for all periods and all forests. Symmetry convention is to operate on
`mainTerm` (whole channels), not to assume the chosen path algorithm equivariant.
Recovery of **symbol0** uses the all-`n` Floor (in fact `n=1` suffices) and is
exact. Width payment includes the four edges of the plaquette.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin
open Lattice RG  Wilson Precision Tree Exterior Bloch Laurent 
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius

/-- Will fill in the cubic/quartic arrays later. Also the initial **loop** array (not
assumed a consistent *solution* loop array under iterations!). -/
def blank (G : Gauge) (k : ℕ) : ℕ → Atom G k := fun _ =>
  ⟨fun _ => ⟨[],⟨(0,1),by decide⟩⟩,0⟩





def foot (p : PlaqAxes) (x : Cover) : Slot := ⟨route 0 x (Equiv.refl Axis),p⟩
@[simp] theorem foot_stop (p : PlaqAxes) (x : Cover) : (foot p x).offset=x := route_end ..
@[simp] theorem foot_length (p : PlaqAxes) (x : Cover) : (foot p x).length=size x+4 := by
  simp [foot,Slot.length,route,axisRoute,straight,allAxes,size,Axis,Fin.sum_univ_succ,List.finRange_succ]

def index (α : Type) [Countable α] [Infinite α] : ℕ ≃ α := by
  letI := Classical.choice (nonempty_denumerable α); exact (Denumerable.eqv α).symm
abbrev Address := PlaqAxes × Cover
private instance ip : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩
def tags : ℕ ≃ Address := index _

def coreRow (B : Bed) (p : PlaqAxes) (i : ℕ) : ℝ × Slot :=
  let a:=tags i; (B.roots (plaquette p) (plaquette a.1) a.2,foot a.1 a.2)



variable {G : Gauge} {B : Bed}
















end YM.Progress.ClassicalKin
