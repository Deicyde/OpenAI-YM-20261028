import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.ODE.ExistUnique
import YM.Bid.Fuels
import YM.Next.UV_STRESS.Across
import YM.Pressure.Seeds

set_option warningAsError false

/-!
# A one-step mixed recurrence with NO loss of stored support exponent

Proposal for THIS all-h-copy query in the lens wallets of UV_STRESS.
Not a theorem that such one-step bounds hold; see `Kiln` for the exact
physical asks. Importantly the red bounds are *not* asked to do the
propagation to the stop. Here open up the iteration. Provisional output
marker radius t at each transaction, ordinary input radius R. Ask for
regeneration of *output* exponential reserve at the provisional radius;
can't spend an additional exponent from input at each step and just
assert all such inputs persist. Similarly test order. Shape buys back the
marker radius and pays explicit `loss` for the transaction; no factorial
radius cut except where evaluating (i.e., the smaller Radial wallet is
**not** being used to fund the next step).

One way to put numbers on the red calculation is a column-sum bound on
positive rooted descendants (all transfer histories **including vacuum
costs**, keep full supports). Includes weighted matrices version to take
those kinds of estimates; strength/regeneration across actual histories
outstanding. A numerical authentication of the exponents/factors in this
receipt does NOT assert this bound physically, in particular when the output
lens or reserved exponent is as strong as the actual input wallet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PhaseCoarse
open Function Set Filter MeasureTheory Analysis Lattice Wilson RG Overlay Marker Next.UVStress Mix
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

section tools
variable {α β γ : Type*}











/-- Charge any number of output labels to a summable list of input
addresses. No *row* sum asked of the engine; only columns, uniform in
input address, and positive coefficient domination. Can bear sums over
multiple-input trees rolled into `freight j i`, with e.g. i designating
the unique node bringing the prescribed root, all its siblings already
paid for by a small-input hypothesis below; not an assumption of linearity
of the physics. -/
structure Manifest (inp : α → ℝ) (out : β → ℝ) (loss : ℝ) where
  freight : β → α → ℝ
  load i : SumBudget (fun j => freight j i) loss
  packed j : out j ≤ ∑' i, freight j i * inp i


end tools

variable {n : Side} {G : Gauge} {P : Rep G n} {V : Type} [DecidableEq V] {R : Census V}
  {A : Bands R P} (T : Stubs A)

/-- Scalar unit plus regular & K strips, split by singleton and mixed keys. -/
abbrev Address := ℕ ⊕ (ℕ × ℕ)
abbrev Way := Unit ⊕ Address

def cruise (i : V) (w q : ℝ) (b : Bool) (j : ℕ) :=
    if ranked (A.rays j)=b ∧ i∈(A.rays j).val then T.crown (fun _ => w) q j else 0

def landing (i : V) (w q : ℝ) (b : Bool) (j : ℕ×ℕ) :=
    if ranked (A.marks j.1 j.2)=b ∧ i∈(A.marks j.1 j.2).val then T.cord (fun _ => w) q j else 0

/-- No summing over possible root anchors. In the stronger forced ledger
may want to inflate `landing` by inverse varkappa (then, to use these
quotes, debit any conversions). -/
def tariff (i : V) (w : ℝ) : Way → ℝ :=
    Sum.elim (fun _ => w*‖A.units i‖)
      (Sum.elim (fun j => cruise T i w 0 false j+cruise T i w 0 true j)
        (fun j => landing T i w 0 false j+landing T i w 0 true j))












variable [Fintype V]
section next
variable {m : Side} {L : Rep G m} {B : Bands R L} (Q : Stubs B)

/-- Need
column flexibility because gas/germ transfer can switch between forced and
regular.

Functional Integral versions of steps separately in Kiln.

Data
may, of course, only be obtained *after combining signs* (cf. signed-source
addresses) and one output can debit actual hit contributions rolled up
from arbitrarily many overlapping inputs.

In particular a crude `Manifest`
using unconditioned absolute density bounds per sector is not expected
to work here. -/
structure Customs (wi wp θ loss : ℝ) where
  air (i : V) : Manifest (tariff T i wi) (cruise Q i wp θ true) loss
  ground (i : V) : Manifest (tariff T i wi) (landing Q i wp θ true) loss

def cutRate (s m loss x : ℝ) := (x^2)⁻¹*(loss*(s+(s+m+(s+m))))


end next

section level
variable {C : Family G} {N p : ℕ} {m : ℕ}





end level
end YM.UVNext.PhaseCoarse
