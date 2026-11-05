import YM.Push.PRICE_COMPILER.Basic
import YM.Work.C02
import YM.Work.G07.Stencil

/-!
# Numerical rates for path and support budgets

For these widths get pre-L quote numbers for the
`r34cap`-style inequalities; with them fix the caps.

Then take pre-L kinetic
error bounds and loop transfer costs and width-fit asks (like
`C_J η/L ≤ σ_J/2`), which can now use those widths/caps.

All gates costed
here work for all sufficiently large L.

None uses any actual block lengths
in another stage to set a LOWER bound on this stage's L.

This doesn't prove the physics bounds/identities **at** these costs. See
later path consumer in this project for the actual required estimates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG Wilson RG.Supply 
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-- Early quote. Can already include finite internal losses on an edge; it
is availability *after* those. May shrink each input by any further width
requirements **known before** the L gates; don't use a report after taking
the corresponding lengths. -/
structure Openings where
  born : ℕ → ℝ
  transfers : ℕ → ℕ → ℝ
  wish : ℕ → ℝ -- also cap the width by this (arbitrary positive)
  bp i : 0 < born i
  tp j i : 0 < transfers j i
  wp i : 0 < wish i

namespace Openings
variable (t : Openings)
/-- Commit a width for BOTH sides of every use. Also leave room for finite
moments at each j, not a repeated width erosion. -/
def offered (i : ℕ) : ℝ := min (min (t.wish i) (t.born i)) (intoMin t.transfers i)

def active (i : ℕ) : ℝ := rateLo t.offered i / 2

lemma active_anti : Antitone t.active := fun i j hij =>
  div_le_div_of_nonneg_right (rateLo_anti _ hij) (by norm_num)

lemma active_pos (i) : 0 < t.active i := div_pos (rateLo_pos
  (fun j : ℕ => lt_min (lt_min (t.wp j) (t.bp j)) (lt_min (t.tp ..) (t.tp ..))) _) (by norm_num)

lemma offered_ge (i : ℕ) : 2 * t.active i ≤ t.offered i := by
  unfold active
  linarith only [rateLo_le t.offered i]

lemma born_ge (i : ℕ) : 2 * t.active i ≤ t.born i :=
  (t.offered_ge i).trans ((min_le_left ..).trans (min_le_right ..))

lemma transfers_ge {i j : ℕ} (h : StepStages j i) : 2 * t.active i ≤ t.transfers j i :=
  (t.offered_ge i).trans ((min_le_right ..).trans (intoMin_le t.transfers h))

lemma wish_ge (i : ℕ) : 2 * t.active i ≤ t.wish i :=
  (t.offered_ge i).trans ((min_le_left ..).trans (min_le_left ..))
end Openings

/-- Next set of raw quotes (unified amount okay to be larger). After
committing widths. BEFORE fixing caps or quoting the kinetic error. -/
structure Amounts where
  born : ℕ → ℝ
  sends : ℕ → ℕ → ℝ
  extra : ℕ → ℝ
  born_pos i : 0 < born i
  sends_pos j i : 0 < sends j i

namespace Amounts
variable (t : Amounts)

def offered (i : ℕ) := max (max (t.extra i) (t.born i)) (intoMax t.sends i)

/-- One cap for all rows/classical coefficients in `PathData.Bounds`. -/
def active (i : ℕ) : ℝ := 4*payHi t.offered i

lemma active_pos (i : ℕ) : 0 < t.active i := mul_pos (by norm_num) (payHi_pos ..)
lemma active_mono : Monotone t.active := fun _ _ hij => mul_le_mul_of_nonneg_left (payHi_mono t.offered hij) (by norm_num)



lemma born_le (i : ℕ) : t.born i ≤ t.active i := calc
  _ ≤ payHi t.offered i := le_trans ((le_max_right ..).trans (le_max_left ..)) (le_payHi t.offered i)
  _ ≤ _ := le_mul_of_one_le_left (payHi_pos ..).le (by norm_num)

lemma sends_le {j i : ℕ} (h : StepStages j i) : 4*t.sends j i ≤ t.active i :=
  mul_le_mul_of_nonneg_left
    (le_trans ((le_intoMax _ h).trans (le_max_right ..)) (le_payHi t.offered i)) (by norm_num)
end Amounts

/-- E `r34cap` shape, using a common `R` covering the path row, cubic
and quartic. Cubic quote `A*(1+μ²R)` bounded by this one. -/
def classicalCost (A L R : ℝ) : ℝ :=
    A*(1+L⁻¹^(2:ℕ)*R+ L⁻¹^(4:ℕ)*R^2+L⁻¹^(4:ℕ)*R)







/-- Take only after classical caps. `inputStrip` stands for the width
consumption numerator (scaling like `C_J η` on fine phases), not a
statement of any analytic estimate. -/
structure LoopPrices where
  inputStrip : ℕ → ℕ → ℝ  -- pre-L quote, for classical & loops
  add : ℕ → ℕ → ℝ
  send : ℕ → ℕ → ℝ
  kineticErr : ℕ → ℕ → ℝ -- slope correction bound for each transition
  add_pos j i : 0 < add j i
  send_pos j i : 0 < send j i
  err_pos j i : 0 < kineticErr j i
  input_pos j i : 0 < inputStrip j i

namespace LoopPrices
variable (v : LoopPrices)

def drift := payHi fun j => fromMax v.kineticErr j + 1


/-- Variable loop-cap bound. E `b2loop` , allow different
constants. -/
def cost (j i : ℕ) (L Λ : ℝ) := v.add j i * L^(4:ℕ) + v.send j i / L^(2:ℕ) * Λ


end LoopPrices

/-- Support-projection budget quotes for each transition. `rad` is the
halo measured in **output B units** and quoted PRE-L. `allow` is an
extra output support exponent for the use. -/
structure HaloBill where
  rad : ℕ → ℕ → ℕ
  allow : ℕ → ℕ → ℝ
  extra j i : 0 ≤ allow j i

def haloC (s : ℕ) : ℝ := (((s+6)+(s+6)+1)^4 : ℕ)


/-- Explicit pre-L inequalities on ONE transition (arguments j→i).
`A` support exponent by stage; do not confuse with the classical cost.
For kernel thresholds and all further asks one must **also** raise the
floor in the calendar. -/
structure EdgeGate (A : ℕ → ℝ) (w : Openings) (u : Amounts) (t : LoopPrices) (b : HaloBill)
    (j i L : ℕ) : Prop where
  size : 0 < L
  phase : t.inputStrip j i / L ≤ w.active j / 2
  cap : classicalCost (u.sends j i) L (u.active j) ≤ u.active i
  loopTransfer : t.send j i / (L:ℝ)^2 ≤ 1/4
  covers : 10*haloC (b.rad j i)*(A i+b.allow j i)/L < A j/2



lemma EdgeGate.eventual (A : ℕ → ℝ) (hA : ∀ j, 0 < A j) (w : Openings) (u : Amounts) (t : LoopPrices) (b : HaloBill)
    {j i : ℕ} (h : StepStages j i) : ∀ᶠ L in atTop, EdgeGate A w u t b j i L := by
  have hu := u.sends_le h
  have hl : Tendsto (fun k : ℕ => (k:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hr (x : ℝ) : Tendsto (fun k : ℕ => x / (k:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hl.const_mul x
  have hs (x : ℝ) : Tendsto (fun k : ℕ => x / (k:ℝ)^2) atTop (𝓝 0) := by
    simpa only [inv_pow, div_eq_mul_inv, zero_pow two_ne_zero, mul_zero] using (hl.pow 2).const_mul x
  have ht : Tendsto (fun k : ℕ => classicalCost (u.sends j i) k (u.active j)) atTop (𝓝 (u.sends j i)) := by
    unfold classicalCost
    let R := u.active j; let y := u.sends j i
    have he := ((((tendsto_const_nhds (x:=(1:ℝ))).add ((hl.pow 2).mul_const R)).add
      ((hl.pow (4:ℕ)).mul_const (R^2))).add ((hl.pow (4:ℕ)).mul_const R)).const_mul y
    simpa only [OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, zero_pow, zero_mul, add_zero, mul_one]
      using he
  have hd := u.sends_pos j i
  filter_upwards [eventually_gt_atTop 0,
    (hr (t.inputStrip j i)).eventually (ge_mem_nhds (div_pos (w.active_pos j) (by norm_num : (0:ℝ)<2))),
    ht.eventually (ge_mem_nhds (show u.sends j i < u.active i by linarith only [hd,hu])),
    (hs (t.send j i)).eventually (ge_mem_nhds (show (0:ℝ)<1/4 by norm_num)),
    (hr (10*haloC (b.rad j i)*(A i+b.allow j i))).eventually
      (gt_mem_nhds (div_pos (hA j) (by norm_num : (0:ℝ)<2)))] with L hL hq hR hJ hb
  exact ⟨hL,hq,hR,hJ,hb⟩

theorem edgeFloors (A : ℕ → ℝ) (hA : ∀ j, 0 < A j) (w : Openings) (u : Amounts) (t : LoopPrices) (b : HaloBill)
    (f₀ : ℕ → ℕ) : ∃ f : ℕ → ℕ, Monotone f ∧ f₀ ≤ f ∧ ∀ j L, f j ≤ L →
      ∀ i, StepStages j i → EdgeGate A w u t b j i L := by
  apply collect_upper f₀ (fun j L => ∀ i, StepStages j i → EdgeGate A w u t b j i L)
  exact fun j => eventually_transitions j atTop _ fun _ he => EdgeGate.eventual A hA w u t b he

/-! New Clip: change ONLY `relaxation`, pre-L but after the rate budget is
known. `extra` can include all needed pre-L lower bounds. -/
namespace Openings
variable (w : Openings)

def relax (u : ℕ → Clip) (extra : ℕ → ℝ) : ℕ → ℝ := payHi (fun i =>
  max (max (u i).relaxation (extra i)) (12/w.active i))

def newClip (u : ℕ → Clip) (extra : ℕ → ℝ) (i : ℕ) : Clip :=
    { (u i) with relaxation := w.relax u extra i, radius_pos := payHi_pos _ i }

lemma relax_ge (u : ℕ → Clip) (extra : ℕ → ℝ) (i : ℕ) :
    let v := (w.newClip u extra i).relaxation
    (u i).relaxation ≤ v ∧ extra i ≤ v ∧ 12 ≤ v * w.active i := by
  intro v
  have he : max (max (u i).relaxation (extra i)) (12 / w.active i) ≤ v :=
    le_payHi (fun i => max (max (u i).relaxation (extra i)) (12/w.active i)) i
  rw [max_le_iff, max_le_iff] at he
  exact ⟨he.1.1, he.1.2, (div_le_iff₀ (w.active_pos i)).mp he.2⟩
end Openings
end YM.Push.PriceCompiler
