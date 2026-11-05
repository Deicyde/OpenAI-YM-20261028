import YM.Next.UV_STRESS.Fuse
import YM.Next.UV_STRESS.Least

/-!
# Shell consumes actual fusion energy budgets

True all-copy T at arbitrary m-grid y in annulus with offset. Because we need
only T in weight 4 no E equation differences have been inserted between that
and the left of our comparisons. In E-inspired budgeting a producer of
`Portion` here will, e.g., have to charge offsets of these visible roots (and
prove any branch formula for fusion/old multi-source inputs for *them*, not
just on auxiliaries). If the claim of E that already I_4=0 and ref→Maxwell
quotient injection at weight 4 stands, expect not to need the Haar-equation
auxiliaries of that argument here. Even then a detector argument on Q at
actual offsets plus payments on shifted history will likely be needed. NOT
claiming `Portion` constructed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Overlay Marker Cells RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G)
variable {N p ℓ k h m r j d D : ℕ}







/-- Alternative lower boundary for node estimates: still must afford a
    full signed density join and continue it to actual surveyed costs at
    another stop. Boundedness on counterterm after reference not assumed. -/
structure FusePrice (vN D h k : ℕ) (F : Extraction.Order) {d : ℕ} (J : (N p : ℕ) → Site (C.side N p) → C.book.Ref 4) (v : C.book.Ref d) (e : ℝ)
    (R : TicketR) : Prop where
  ready : C.ref D ≤ k
  -- quotas can be per-node; same layouts pay root stop
  rents (m : ℕ) (y : Cover) (he : C.S.gridPoint m y ∈ annulus e) :
    ∃ (P : ℝ) (K : ℕ×ℕ→ C.book.Ref D), F.late fun N p => ∃ hn : vN+1≤N,
        quota C D k N p (K (N,p)) ≤ P ∧
        ∃ (L : Overlay.Lane C.path (triple (Site (C.side vN p))) N p) (X : Stair C (trays C vN p) N p),
          Portion C L X h D d k R.stop ∧ (X.representation R.stop).Radial (fun _ => R.weight) R.u R.c R.d' R.b ∧
          ∀ i, L.uses (i,0)=(terrace C.S vN hn p).copy i (C.seen ⟨4,J N p (location C.S m N p y)⟩ (location C.S m N p y)) ∧
            L.uses (i,1)=(terrace C.S vN hn p).copy i (C.seen ⟨d,v⟩ 0) ∧
            L.uses (i,2)=(terrace C.S vN hn p).copy i (C.seen ⟨D,K (N,p)⟩ 0)






end YM.Next.UVStress
