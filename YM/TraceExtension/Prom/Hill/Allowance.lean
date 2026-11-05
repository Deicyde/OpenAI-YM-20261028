import YM.Next.RANK.Allowance
import YM.TraceExtension.Prom.Hill.Coordinates
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.Next.RANK.Allowance for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Ship
open Function Set Filter RG MeasureTheory Wilson Cells Glyph Exponential Lattice Read Station
open scoped Topology BigOperators

variable {G : Gauge} (A : Levels G) (M k : ℕ)

-- Needed universally only at the memory allocation for *this* query; entirely numeric.

-- Bench allocation before usage. Also paying *other* numerical and estimate gates
-- at C is still needed in practice! RRequirements.
structure AllocatedSky (O : HaarBudget G) (b : ℝ) : Prop where
  permitted : AllowedSky A b k
  charge : ticket O (A.params (Station.widthSky A b k)) M ≤ pot A M k

variable {C : Family G} (b : ℝ)

def yardSky (C : Family G) {k N : ℕ} (b : ℝ) (hN : k ≤ N) (p : ℕ) : Tiling (C.side N p) :=
  let A := C.path.levels
  center C.S (m:=widthSky A b k) p (((Station.widerSky A b k).trans (beforeSky A b k)).trans hN) 0

section
variable {M k b} {N p m n : ℕ} {x : Points n}

lemma fittingSky {a : Levels G} (h : FitSky a b k x) : tested a b k x ∈ conf _ := by
  apply generic_conf
  exact Market.vision _ (inv_pos.mpr (gap_pos a ..)) _ h.usable

def targetsSky (C : Family G) (B : Fin n → (standard C).Tag) (hx : FitSky C.path.levels b k x) :=
    cumulants C (tested C.path.levels b k x) B (fittingSky hx)

def invoiceSky (B : Fin n → (standard C).Tag) (t : Fin n → C.book.Token) (hx : FitSky C.path.levels b k x) (N p : ℕ) : Config G (C.side N p) → veil (Fin n) :=
  Read.cylinder (targetsSky C B hx) (clients C t b k N p x)

lemma bill_contSky (B : Fin n → (standard C).Tag) (t : Fin n → C.book.Token) (hx : FitSky C.path.levels b k x) (N p) (s) : Continuous
    fun U => (invoiceSky B t hx N p U).part s := Read.cylinder_cont _ (fun i => Read.probes_cont i) s _

/-- A propagated marker purchase on the given course. Notice is value-local,
with any necessary exponent on that `Rep`. -/
def estimateSky (P : Rep G (C.side (widthSky C.path.levels b k) p)) (c : Course C N p k) (hN : k≤N)
    (x : Points n) (Y : Config G (C.side N p) → veil (Fin n)) (e L l r : ℝ) :=
    let A := C.path.levels
    let T := yardSky C b hN p
    let hi : widthSky A b k ≤ N := ((widerSky A b k).trans (beforeSky A b k)).trans hN
    Value.Notice P (fun z => ancestor C.S p (widthSky A b k) hi (stampSiteSky C b x hN p z))
      (c.flow (Array.stamp T (C.beta N p) Y) _ hi) (fun _ => r) e L l

end
end YM.Next.Rank.Ship
