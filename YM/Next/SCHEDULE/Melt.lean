import YM.Next.SCHEDULE.Pour

/-!
# Final stage profile

The given arrays are *numbers*, supplied after `commit` but before any rolls.
Order `Strips`, `width` calculation, `Figures` (classical cost calculation),
`cap`, then `Finish` (with relaxation first, then compute costs depending on
relaxation). All are genuine numeric forecasts, no implication that a
physics estimate really fits them; instead, see the application lemmas here
and later for budgets that can be financed IF fitting the estimates. In
particular test carefully `emits`: has to be achievable at a pre-L width
known before choosing the working widths. Cyclic shrinkage along arbitrarily
long plateaus not allowed. Source Credit on the other hand HAS uniform
estimates already and the budget entries here pay them (on these same frames).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter RG RG.Supply Bid Precision Function Finset

/-- Path strip rates. `loads/L` required from an input (can include all path
powers/phases in fixed computations); `emits` refers to actual attainable
output path width including completing the quartic jet, all loop operations,
for both incoming transitions and top separately. These may depend on the linear
data ceilings and widths, not yet on their own working path widths. -/
structure Strips where
  launch : ℕ → ℝ
  emits : ℕ → ℕ → ℝ
  loads : ℕ → ℕ → ℝ
  top_rate j : 0 < launch j
  rate j i : 0 < emits j i
  nonneg j i : 0 ≤ loads j i

namespace Strips

/-- Buy the minimum of the widths at the three entrance calls:
`top(j), j→j, j+1→j`. That's it, not a limit over depths. -/
def width (q : Strips) (j) := min 1 (min (q.launch j) (min (q.emits j j) (q.emits (j+1) j)))

lemma wp (q : Strips) (j) : 0 < q.width j := lt_min zero_lt_one (lt_min (q.top_rate j) (lt_min (q.rate j j) (q.rate (j+1) j)))
lemma le_top (q : Strips) (j) : q.width j ≤ q.launch j := le_trans (min_le_right ..) (min_le_left ..)
lemma le_pair (q : Strips) {i j} (h : Adj j i) : q.width i ≤ q.emits j i := by
  refine le_trans (le_trans (min_le_right ..) (min_le_right ..)) ?_
  rcases h.cases_forward with rfl|rfl
  · exact min_le_left ..
  exact min_le_right ..
end Strips

/-- Cost at top (launch) and for the classical output with explicit input
power costs multiplying `classic j i`. Choose after width j known for all j.
Includes row and layer costs at the actual widths. -/
structure Figures where
  beginCost : ℕ → ℝ
  classic : ℕ → ℕ → ℝ
  pos j : 1 ≤ beginCost j
  pos_ij j i : 1 ≤ classic j i

namespace Figures
def current (q : Figures) (j) := max (q.beginCost j) (max (q.classic j j) (q.classic (j+1) j))

/-- Single cap for both cubic & quartic. -/
def cap (q : Figures) (j) := 5*(worth q.current).K j

lemma cp (q : Figures) (j) : 1 ≤ q.cap j := by have := (worth q.current).prices j; unfold cap; linarith

lemma le_top (q : Figures) (j) : q.beginCost j ≤ q.cap j := by
  unfold cap
  have := le_trans (b:=q.current j) (le_max_left ..) (worth_ge q.current j)
  have hx := q.pos j; linarith

lemma le_pair (q : Figures) {i j} (h : Adj j i) : 5*q.classic j i ≤ q.cap i := by
  refine mul_le_mul_of_nonneg_left (le_trans ?_ (worth_ge q.current i)) (by norm_num)
  refine le_max_of_le_right ?_; rcases h.cases_forward with rfl|rfl
  · exact le_max_left ..
  exact le_max_right ..
end Figures

/-- `selector` is an extra minimum for R₀ beyond `12/width` (can use the
prior caps). Everything else here may use that R₀. `number` is the
**absolute error** from the logarithmic slope for α. -/
structure Finish where
  selector : ℕ → ℝ
  loop : ℕ → ℕ → ℝ
  number : ℕ → ℕ → ℝ
  W : Worth
  extraColumn : ℕ → ℝ
  loop_pos j i : 1 ≤ loop j i
  drift_nn j i : 0 ≤ number j i

structure Quote where
  widths : Strips
  classicalCost : Figures
  finish : Finish

variable {G : Gauge}

namespace Survey
variable (S : Survey G) (q : Quote)

/-- Relaxation can and may need to be very large. -/
def change (q : Quote) (i : ℕ) := max (12/q.widths.width i) (q.finish.selector i)

lemma change_ge (q : Quote) (i : ℕ) : 12 ≤ change q i := by
  refine le_trans ?_ (le_max_left ..); apply (le_div_iff₀ (q.widths.wp i)).mpr
  have h : q.widths.width i ≤ 1 := min_le_left ..; linarith

/-- Finite credit exposed through stage i. Can charge some as yet unadmitted
weights as well; this is only cost. -/
def supCost (i : ℕ) := (range (i+1)).sup (fun d => Nat.ceil (S.B.fee d (S.o.k i) (S.o.P i)))

def desired (i : ℕ) : ℝ :=
  max (max (Nat.factorial (S.o.k i) : ℝ) (S.supCost i)) (max (64*(q.finish.W.K (i+1))^2) (q.finish.extraColumn i))

def columns := (worth (S.desired q)).K

def melt (j : ℕ) : Stage where
  clip := { (S.sheet.profile j).clip with relaxation := change q j, radius_pos := show 0<change q j from lt_of_lt_of_le (by norm_num) (change_ge q j) }
  order := S.o.k j
  power := S.o.P j
  supportExponent := S.o.A j
  width := q.widths.width j
  paths := q.classicalCost.cap j
  drift := max (q.finish.number j j) (q.finish.number j (j-1)) + 1
  columns := S.columns q j
  order_ge := S.o.six j
  power_ge := S.o.two j
  width_pos := q.widths.wp j
  price_pos := S.o.pos j
  paths_pos := lt_of_lt_of_le zero_lt_one (q.classicalCost.cp j)
  columns_ge := (worth (S.desired q)).prices j
  drift_ge := add_nonneg (le_max_of_le_left (q.finish.drift_nn j j)) zero_le_one
  slow_selector := by
    have hh : 12/q.widths.width j ≤ change q j := le_max_left ..
    exact (div_le_iff₀ (q.widths.wp j)).mp hh

/-- `v` still must satisfy joint floors. -/
def paper (v : ℕ → ℕ) : Sheet G :=
  { S.sheet with
    profile := S.melt q, floorL := v,
    orders := S.o.dk, powers := S.o.dP, prices := S.o.dA }

lemma forecast (v) : Refining S.sheet (S.paper q v) := by
  refine ⟨rfl,fun _ => rfl,fun i ↦ ?_,fun _ => (S.melt q _).drift_ge⟩
  exact ⟨q.classicalCost.cp i,min_le_left ..,(worth (S.desired q)).prices i, change_ge q i,le_rfl⟩

def metals (K : MapPrices) (v : ℕ → ℕ) : Org.Metals G :=
  ⟨S.paper q v,K,S.B.chart,S.B.chartRatio⟩

lemma drift (i j) (h : Adj j i) : q.finish.number j i + 1 ≤ (S.melt q j).drift := by
  refine add_le_add_left ?_ 1
  rcases h.cases_back with h|h <;> rw [h]
  · exact le_max_left ..
  exact le_max_right ..

lemma factorial (i) : (Nat.factorial (S.o.k i) : ℝ) ≤ (S.melt q i).columns :=
  le_trans (le_max_of_le_left (le_max_left ..)) (worth_ge (S.desired q) i)

lemma ahead (i) : 64*(q.finish.W.K (i+1))^2 ≤ (S.melt q i).columns :=
  le_trans (le_max_of_le_right (le_max_left ..)) (worth_ge (S.desired q) i)

lemma credit (d j) (h : Admits S.requests j d) : Credit (S.B.entry d) (S.o.k j) (S.o.P j) (S.melt q j).columns := by
  have he := le_trans (show (S.supCost j:ℝ) ≤ S.desired q j from le_max_of_le_left (le_max_right ..)) (worth_ge (S.desired q) j)
  have hh : (S.B.fee d _ _) ≤ (S.melt q j).columns := le_trans (Nat.le_ceil (S.B.fee d (S.o.k j) (S.o.P j))) (le_trans ?_ he)
  case refine_1 =>
    have hd : Nat.ceil (S.B.fee d (S.o.k j) (S.o.P j)) ≤ S.supCost j :=
      le_sup (f:=fun d => Nat.ceil (S.B.fee d (S.o.k j) (S.o.P j))) (mem_range.mpr <| by have := h.1; omega)
    exact_mod_cast hd
  intro p hp hl n o i
  obtain ⟨ht,hi,H⟩ := S.B.credit d _ _ p hp hl n o i
  have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ p.threshold^(((S.B.frames.level d).grades i).2) from pow_nonneg p.threshold_pos.le _)
  exact ⟨ht,hi.trans hm,fun x hx a ha hb => (H x hx a ha hb).trans hm⟩
end Survey
end YM.Next.Scheduling
