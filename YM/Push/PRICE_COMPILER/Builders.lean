import YM.Push.PRICE_COMPILER.Flows

/-!
# Tying symbolic path estimates into an on-demand induction

If not yet holding a whole path series, can also use Permit for finite
path continuations. Exposure of the local remaining inputs AFTER price
order. Not a proof of any of those producer estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function RG Lattice RG.Supply Pressure Precision Bid Tree
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

/-- E top price SHAPE with a specific W.
Supply e.g., with unmasked Wilson realization on permitted levels. -/
def StartsBudget (P : Before) (a : Levels G) (N : ℕ) (R : PathData G) :=
    let j := a.clock.J N
    let b := a.params N
    let C := P.amount.born j
    2*b.width ≤ P.opening.born j → Normalized R b.clip ∧ PathMass R b.width C 0 C C

/-- Per-run construction hooks. The step is asked only when the *input*
resource has already met the terms. `Ready` is on actual objects; can
make stronger requests if needed internally. Cannot merely define e.g.,
`first` in terms of the desired Estimation conclusion: a producer must
produce the actual `∃` together with the RawPath data and all needed
continuation proofs. `keeps` analogous. For all period comparisons etc,
`q` can encode per-edge data and one can use the results to spend for this
same system.
-/
structure PathBuilder (P : Before) {a : Levels G} (V : Horizon a)
    (Ready : ℕ → ℕ → PathData G → Prop) (q : ℕ → ℕ → PathData G → PathData G → Prop) : Prop where
  first (N : ℕ) : ∃ R, StartsBudget P a N R ∧ Attached (V.H N N) R ∧ Ready N N R
  step N m : m < N → ∀ R, Ready N (m+1) R → Attached (V.H N (m+1)) R → Budgeted a (m+1) R →
    ∃ S, TransferPrices P a m R S ∧ Attached (V.H N m) S ∧ Ready N m S ∧ q N m R S

namespace Permit
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
    {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (h : Permit M I a)
include h




end Permit
end YM.Push.PriceCompiler
