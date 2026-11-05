import YM.Next.RANK.Allowance
import YM.Next.RANK.Matrices

/-!
# From the terminal local finite estimates to purchases

Conditional Vertical step to the end prices from a law-level estimate gate.
Here is the price of one weight. Exposes a station scheme (k of a specific
cost), a linear readout quota and unnormalized-push price tests. See subsequent production through the physics prerequisites (e.g.
marked-step attachment costs) in this project; not assuming arbitrary A/B/C trajectories compose. Don't treat the
Frequently part as satisfiable independently of the weighted estimates IN it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Ship
open RG Lattice Wilson Cells Read Station Price Glyph Filter Set Market Extraction
open scoped Topology BigOperators

variable {G : Gauge} {d N p k : ℕ}
variable {C : Family G} {S : Table C.book} (O : HaarBudget G) {X : Columns C S d} (p' : Representatives C X) (b : ℝ)

def ranksheet (X : Columns C S d) (v : Fin (X.dim+1) → C.label d) (i : Fin X.amount) (j : Fin (X.dim+1)) (s : Fin ((X.row i).extra+1)) : C.book.Token :=
    ⟨d,v (Columns.Trials.names (X:=X) i j s)⟩

def Bill (X : Columns C S d) (P : Rep G (C.side (width C.path.levels b k) p))
    (Y : Course C N p k) (hN : k≤N) (v : Fin (X.dim+1) → C.label d) : Prop :=
    ∀ (i) (h : Fit C.path.levels b k (X.row i).expected) j,
      ∃ e : ℝ,0 ≤ e ∧ estimate P Y hN (X.row i).expected
        (invoice (roles X i j) (ranksheet X v i j) h N p) e 1 1 (allowance C.path.levels 2 k)







-- Include lifts explicit even for later usage/ancestry compatibility beyond Purchases scope.

structure Travels (Z : X.Trials) : Prop where
  occupied (i : ℕ) : Allocated C.path.levels 2 (Z.depth i) O b
  width (i : ℕ) : Z.width i=Station.width C.path.levels b (Z.depth i)
  testScale (i : ℕ) : Z.scale i=Station.gap C.path.levels b (Z.depth i)
  mark (i j) : Z.mark i j = Station.choose C.path.levels b (Z.depth i) (X.row j).expected
  cost (i : ℕ) : Z.gap i=Ship.budget C.path.levels 2 (Z.depth i)
  fits (i j) : Fit C.path.levels b (Z.depth i) (X.row j).expected
  starts (i : ℕ) : C.ref d ≤ Z.depth i
  name_at (i : ℕ) : ∀ᶠ N in atTop, ∃ hN : Z.depth i≤N, ∀ p,
    let A := C.path.levels; let k := Z.depth i
    ∃ (read : C.label d→ₗ[ℂ] C.label d), Tested C d k N p read ∧ Names C p' (mag A b k) k N p read (Z.lift i N p) ∧
      ∃ (Y : Course C N p k) (P : Rep G (C.side (Station.width A b k) p)),
        Settled P Y (((wider A b k).trans (before A b k)).trans hN) ∧
          Bill b X P Y hN (Z.lift i N p)



-- extract useful sequence. keep p' & b & X.


end YM.Next.Rank.Ship
