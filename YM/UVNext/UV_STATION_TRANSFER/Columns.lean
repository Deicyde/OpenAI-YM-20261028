import YM.UVNext.UV_STATION_TRANSFER.Tests

set_option warningAsError false

/-!
# Build a linear station lift with the real and signed laws

E representation clauses near  and . Columns are actual Family
reference coordinates (not raw Wick operators or limiting fields). Check
H and real intertwining only at the chosen arbitrary finite bases (which e.g.
can be chosen real with unit first). Operator bound asked only pointwise on
each of those columns on the same ordered tails. Threshold can vary by k,
by weight, by column. Non-contraction cost OK.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.StationTransfer
open Function Set Filter MeasureTheory Metric Analysis Extraction
open Climb Ward Table Next.UVStress
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {F : Order} {D : ℕ}

abbrev Column (C : Family G) (d : ℕ) := Fin (Module.finrank ℂ ((Bel C.book).Field d))
abbrev Schemes (C : Family G) (D : ℕ) := Series (fun i : Fin (D+1) => (Bel C.book).Field i)
structure Ticket (C : Family G) (D : ℕ) where
  r (k : ℕ) : ℝ
  live (k : ℕ) : 0 < r k
  grid (k : ℕ) : ℕ
  σ (k : ℕ) : ℝ
  pos (k : ℕ) : 0 < σ k
  basis : Schemes C D
  columns (k N p : ℕ) (i : Fin (D+1)) (j : Column C i) : C.book.Ref i

section
variable {α : Type*} [NormedAddCommGroup α] [NormedSpace ℂ α] [FiniteDimensional ℂ α]
    {β : Type*} [NormedAddCommGroup β] [NormedSpace ℂ β] [FiniteDimensional ℂ β]
variable {ι : Type*} [Fintype ι] (B : Module.Basis ι ℂ α)
private def cooperate (f : ι → β) : α →L[ℂ] β := LinearMap.toContinuousLinearMap (B.constr ℂ f)

omit [FiniteDimensional ℂ β] in
private lemma cooperates (f : ι → β) (x : α) : cooperate B f x = ∑ j, B.repr x j • f j := B.constr_apply_fintype ℂ f _
omit [Fintype ι] [FiniteDimensional ℂ β] in
private lemma cooperate_at (f : ι → β) (i) : cooperate B f (B i) = f i := B.constr_basis ℂ _ _

-- eventually bounded, not asking continuity in k

end

namespace Ticket
variable (T : Ticket C D) (H : (Bel C.book).RealSpin)

/-- Column checks. Separated order thresholds for each basis test. -/
structure Right (F : Extraction.Order) (H : (Bel C.book).RealSpin) : Prop where
  tariffs (i : Fin (D+1)) (j : Column C i) : ∀ᶠ k in atTop, ∃ A : ℝ,
    F.late fun N p => ‖T.columns k N p i j‖ ≤ A
  bars (i : Fin (D+1)) (j : Column C i) : ∀ᶠ k in atTop, F.late fun N p =>
    (∑ l,(T.basis i).repr ((Bel C.book).conj H i (T.basis i j)) l • T.columns k N p i l) = star (T.columns k N p i j)
  signed (i : Fin (D+1)) (j : Column C i) (s : Signed) : ∀ᶠ k in atTop, F.late fun N p =>
    (∑ l,(T.basis i).repr ((Bel C.book).mirror H i s (T.basis i j)) l • T.columns k N p i l) =
      C.book.mirrorGroup i s (T.columns k N p i j)
  scalar : ∀ᶠ k in atTop, F.late fun N p =>
    (∑ l,(T.basis (⟨0,Nat.succ_pos D⟩ : Fin (D+1))).repr ((Bel C.book).unit 0) l • T.columns k N p ⟨0,Nat.succ_pos D⟩ l) =
      C.book.scalar 0

def start (k : ℕ) : Wheel C D where
  r := T.r k
  rad := T.live k
  grid := T.grid k
  σ := T.σ k
  stripe := T.pos k
  atCut := fun ⟨N,p⟩ i => cooperate (T.basis i) (T.columns k N p i)







end Ticket
end YM.UVNext.StationTransfer
