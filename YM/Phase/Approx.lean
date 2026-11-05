import YM.Cells.Margins
import YM.Dash.Inert
import YM.Ground.Permute


/-!
# Reflection Grid lemmas

Use one monomial gap difference `A−θ A` with same ordinary-real fields.
Encounter of w itself arbitrary; for `FarAway` use integer t along aligned grid
string all components t incl time. Not θ on scalars. Require exact probability
ordinary square of *these* and controlled pair error using *same* approximants.
Specializes E grid hypotheses. Compares after extraction only, preserving T expected.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Grid
open Function Set Filter MeasureTheory Measure Complex Analysis Extraction Ground Table Row Lattice Wilson Word
open scoped Topology InnerProductSpace NNReal ENNReal ContDiff BigOperators ComplexOrder
variable {G : Gauge} {C : Family G} {S : Table C.book} {N p n : ℕ} {f : Extraction.Order} {V : Chamber S timeAxis}

abbrev Tag (h : ℕ) (v : Fin n → C.book.Token) (x : Fin n → Cover) := Word.realize v (Extraction.Order.grid C h x)

abbrev plain (v : Fin n → C.book.Token) := ∀ i, star (v i).2=(v i).2

/-- Need for SOME large h coordinates, not vacuous itself. L goes through labels after reference.
Point clusters at grid h of any complexity n; approximants for real-combination pairs.
-/
def force (h t i : ℕ) := C.S.gridPoint h (fun _ => t*i)

-- t multiple of h-grid in actual positions

def anti (w : C.book.Word) := Word.act (Signed.mirror timeAxis) w
lemma apart {w : C.book.Word} (hx : distinct w) : distinct (anti w) := by
  unfold anti Word.act; rw [locations,List.map_map]
  simpa only [List.map_map,Function.comp_def] using! ((locations.1 hx).map (Ortho.move_injective (Signed.reflect timeAxis)))

variable (h : ℕ) (v : Fin n→C.book.Token) (x : Fin n → Cover)

/-- ACTUAL A-θA without reordering. θx grid by sign. -/
def tiny (N p : ℕ) (u : Cover) (q : Config G (C.side N p)) :=
    ∏ i, C.seen (v i) (Cells.location C.S h N p (x i+u)) q

def flash (N p t j : ℕ) (q : Config G (C.side N p)) :=
  let D : Cover := fun _ => t*j
  tiny h v x N p D q - tiny h (C:=C) (C.book.move (Signed.mirror timeAxis) ∘ v) ((Signed.mirror timeAxis).act ∘ x) N p D q

/-- at physical h grid. -/
def compareA (t r s : ℕ) (w z : C.book.Word) := S.expect (carry w (force (C:=C) h t r) ++ carry z (force (C:=C) h t s))

def event (t r s : ℕ) :=
  let w := Tag h v x
  ((compareA (S:=S) h t r s w w).re-(compareA (S:=S) h t r s w (anti w)).re)-
    ((compareA (S:=S) h t r s (anti w) w).re-(compareA (S:=S) h t r s (anti w) (anti w)).re)

/-- Uniform in offset t diagonal magnitude (paid later by q) independent q,j
h fixed. Functions not demanded to be translation copies (sufficient simply
for there to be simultaneous approximations with uniform pair tests at all
integer translations, as stated here). For fixed-order J then d,T.
-/
def bill (i j : ℕ) (N p t : ℕ) := ∫ q : Config G (C.side N p),
    (flash h v x N p t i q * flash h v x N p t j q).re ∂law G _ (C.beta N p)
structure Covering (i : ℕ) (v : Fin n→C.book.Token) (x : Fin n→Cover) where
  plots (k : ℕ) (N p t j : ℕ) : Config G (C.side N p) → ℝ
  reserve (k : ℕ) : ℝ
  small : ℕ → ℝ
  grows : Tendsto small atTop (𝓝 0)

namespace Covering
variable (P : Covering h v x)
structure Works (f : Extraction.Order) : Prop where
  controls k t j : f.late fun N p => Measurable (P.plots k N p t j) ∧ ∀ q, |P.plots k N p t j q| ≤ P.reserve k
  fillings (k i j) : i < j → ∀ᶠ t : ℕ in atTop, f.late fun N p =>
    |(∫ q,P.plots k N p t i q * P.plots k N p t j q∂law G _ (C.beta N p))-bill h v x i j N p t| ≤ P.small k
end Covering

/-- Continuum API. Needed separately to use Covering; generic all projections. -/
def Expects := ∀ i j : ℕ, i<j → ∀ᶠ t : ℕ in atTop,
    Tendsto (fun u : ℕ × ℕ => bill h v x i j u.1 u.2 t) f.fuse (𝓝 (event (S:=S) h v x t i j))

end YM.OS.Grid
