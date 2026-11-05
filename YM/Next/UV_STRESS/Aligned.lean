import YM.Bid.Loan
import YM.Next.UV_STRESS.Range

/-!
# Terminal-budget adapter with the actual singleton signed coordinates

One sufficient normal form inside the MANY-source propagation. Not enough to
simply have isolated Duet budgets/density evaluation. In this proposal, the
L has to be attainable *with the corresponding addressing*, using actual
integrand functions at these marks. May use other adapters if not. Does not
solve presence/absence gates or normalization re-centering down a history.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Overlay Marker RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G)
variable {d N p ℓ r k : ℕ} {ι : Type} [DecidableEq ι]

section Scores
variable {α β : Type*}





end Scores

variable {R : Census ι} {A : Bands R (C.path.rep N p ℓ)} (P : Bid.Duet C.path (C.labels.level d) N p r k)

structure GridPattern (P : Bid.Duet C.path (C.labels.level d) N p r k) (A : Bands R (C.path.rep N p ℓ)) (i : ι) where
  joinR : (Stones C d ⊕ ℕ) ↪ ℕ
  locate : ℕ → ℕ
  terms t : A.rays (joinR t) = R.fire i
  ports : P.atPoint ℓ=A.origins i
  units : A.units i=(P.voice ℓ).x 0
  primary t : A.support (joinR (.inl t))=(C.localSection d).footprint (P.atPoint ℓ) ∧
    A.H (joinR (.inl t))=hx_chunk C (N:=N) ℓ (P.voice ℓ) (P.atPoint ℓ) t
  dust t : A.support (joinR (.inr t))=(P.voice ℓ).support t ∧ A.H (joinR (.inr t))=(P.voice ℓ).regular t
  stems (q : ℕ) : A.marks q (locate q)=R.fire i ∧ A.entries q (locate q)=(P.voice ℓ).forced q
  other t : A.rays t=R.fire i → t∉Set.range joinR → A.H t=0
  dead q t : A.marks q t=R.fire i → t≠locate q → A.entries q t=0

def stencil_fee (m : ℕ) := Real.exp (lenses C m).supportExponent*(C.path.levels.params m).columns


end YM.Next.UVStress
