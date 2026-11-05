import Mathlib.Analysis.Calculus.SmoothSeries
import YM.SectorNext.RECONNECTED_LOCALITY.Tendril



set_option warningAsError false

/-!
# Cover-speed evolution of the unrestricted pressure series

 identity proof here with a DIFFERENT analytic parameter and actual
convergence on an open interval larger than [0,1]. Uniform hit convergence from
Tendril (comes from reserved support +2 here; more for
using derivative jets in V later). No analytic truth assumption on *fields* for
the evolution itself, all evaluated at fixed V incl masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Rose
open Function Vouchers Lattice Finset RG Ledger
open scoped Classical

variable {c : Side} {ι : Type*}

/-- Scaling on [-2,2]. -/
def cruise (d : ℕ) (p : ℝ) (x : ℝ) : ℝ := p * x^d








variable (S : ι → Support c) (B : ℕ)

/-- At each admissible λ restrict *the tree list* by its actual union
intersecting the forbidden region. Include the powers on root and every occurrence. -/
def leaf (u : ι → ℝ) (Y : Support c) (i : Rose ι) :=
    if Disjoint (union S i) Y then word S B (-1) u i else 0



def budget (v : ι → ℝ) (a : ℝ) (b : Rose ι) := Real.exp (a*fee S B b)*word S B 1 v b

def Primed (v : ι → ℝ) (a ε : ℝ) : Prop :=
    Climber S B (fun i => Real.exp ((2+a)*coverNumber B (S i))*v i) ε ∧ 0 ≤ a

namespace Primed
variable {S B} {a ε : ℝ} {u v : ι → ℝ} (h : Primed S B v a ε)
include h











private def next (u : ι → ℝ) (a : ℝ) (Y : Support c) (i : ι) (t : Rose ι) :=
    if link S i t then -(cruise (fee S B t) (leaf S B u Y t) a) else 0





end Primed

end YM.SectorNext.Reconnect.Rose
