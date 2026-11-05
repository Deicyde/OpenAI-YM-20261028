import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Costing

set_option warningAsError false

/-!
# Numbers for applying the conditional transfer criteria

Keep dependence on the actual schedule. Plan post-L checks for every required
`stepping`, `Space` etc if constructing a schedule. No assertion these are
feasible for physical producers. Explicit ratio, limit and lower bounds as
sufficient. Used with exact inputs next. No constants in `stepping`
depend on k whose comparison is being requested or N or p or # slots or y.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror.Marketing
open Set Filter Function MeasureTheory RG Wilson Lattice Cells Marker Overlay Tower Net Masked Stop
open Labels Source 
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} (C : Family G)

structure Rates where
  /-- initial cost envelope (remainder) given cutoff-pair epoch k. -/
  top : ℕ → ℝ
  /-- target per-slot and rank-only budgets after transfer to level j. -/
  unit : ℕ → ℝ
  mix : ℕ → ℝ
  /-- at output j, lose on provisional radius and mix cost but give extra
  support in units of actual p cover costs. -/
  loss : ℕ → ℝ
  overspend : ℕ → ℝ
  gain : ℕ → ℝ
  topPos j : 0 < top j
  pure j : 0 < unit j
  rankPos j : 0 < mix j
  lose j : 1 ≤ loss j
  over j : 1 ≤ overspend j
  buys j : 0 ≤ gain j

/-- For using G09, whole budget at top still before exponential decay. -/
def total (S : Rates) (k : ℕ) := 4*(1+(C.path.levels.params k).columns)*S.top k


def income (S : Rates) (j k : ℕ) := (total C S k) / (Bid.gainChart C.path k j)







structure Places (S : Rates) (m d l : ℕ) : Prop where
  level : m ≤ l
  /-- enough for stop entropy estimate on any ONE l. -/
  low : Tendsto (fun k => income C S 0 k) atTop (𝓝 0)
  /-- all positions below this can be used for stronger support. -/
  high j : l ≤ j → 8 ≤ C.path.levels.clock.coverSize j
  generous j : l ≤ j → (C.path.levels.clock.coverSize j:ℝ)^2 ≤ C.S.a m / C.S.a j
  stepping (j) : l ≤ j →
    S.overspend j * (S.unit j / priceOne C d j) * Bid.gainChart C.path (j+1) j ≤
      S.unit (j+1) / priceOne C d (j+1) / S.loss j * Real.exp (S.gain j*(C.path.levels.clock.coverSize j:ℝ)/64)

variable {S : Rates} {m d l j : ℕ}







end YM.ProjectorNext.RMirror.Marketing
