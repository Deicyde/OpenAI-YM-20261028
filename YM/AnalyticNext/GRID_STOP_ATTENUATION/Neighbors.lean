import YM.AnalyticNext.GRID_STOP_ATTENUATION.Currency
import YM.Next.MULTISOURCE.Middle
import YM.Push.RELAY_DIFFERENCE.Estimate
import YM.Push.RELAY_DIFFERENCE.TwoSided

set_option warningAsError false

/-!
# Commit a scale currency and pay two neighboring ratios

From B70's `Tabs` & `Margins`. No aperture in these uses is a function of
probe count or of `N`/period. A reset can recur for arbitrarily long in one
plateau. The radius at an inner step is independent of which function's
representative is purchased at the next; no promise of such representatives
follows from these arithmetic estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Planning
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Stock Asymptotics
open scoped Topology Matrix.Norms.Frobenius BigOperators Asymptotics

variable {G : Gauge} (C : Family G) (δ : ℝ) (i k : ℕ)

def market := Real.exp ((C.path.levels.params i).supportExponent+δ)*(C.path.levels.params i).columns
def coin := (16 * market C δ i)⁻¹
-- Amplification radius, at EACH intervening stage
/-- Have to tune E already uniformly in cutoff/periods on each station k before using. -/
def width (E : ℝ) := coin C δ i / Push.RelayDifference.escrow C k i E

private lemma column_one : (1:ℝ) ≤ (C.path.levels.params i).columns := (C.path.levels.params i).columns_ge



lemma market_one (hδ : 0 ≤ δ) : 1 ≤ market C δ i := Pair.currency_one C.path.levels δ i hδ








private lemma block_one (i : ℕ) : (1:ℝ) < (C.S.block i).val := by
  exact_mod_cast (lt_of_lt_of_le (by norm_num) (C.S.block_large i) : 1 < (C.S.block i).val)

-- Multi.Wage.cheap_column is private
private lemma cheap (i : ℕ) : Real.log ((C.path.levels.params (i+1)).columns) ≤ Real.log (C.S.block i).val := by
  let A := C.path.levels; let X := A.params (i+1)
  have ht := A.fits.logCost i
  have hL := Real.log_pos (block_one C i)
  have he : Real.log X.columns ≤
      Real.log (1+X.paths+X.width⁻¹+X.columns+X.clip.relaxation+X.supportExponent) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one X.columns_ge) (by
      linarith only [X.paths_pos, (inv_pos.mpr X.width_pos), X.clip.radius_pos,X.price_pos])
  refine he.trans ((div_le_iff₀ hL).mp ht |>.trans (mul_le_of_le_one_left hL.le (inv_le_one_of_one_le₀ ?_)))
  have h : (1:ℝ) ≤ A.clock.J (i+1) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 4) (A.clock.adm _))
  exact one_le_pow₀ h

-- Covers even the reverse ratio; Don't just assume growth of columns!
lemma market_bound (hG : G.Simple) (_hδ : 0≤δ) (ht : Tabs C.path.levels) (H : Margins C.path.levels) :
    ∃ M : ℕ, ∀ᶠ i in atTop, Real.log (market C δ i) ≤ M*Real.log (C.path.levels.clock.hatBeta i) := by
  let A := C.path.levels; let f j := Real.log (A.clock.hatBeta j)
  have hA : ∀ᶠ i in atTop, Real.log (A.params i).columns ≤ f i := by
    obtain ⟨m,hm⟩ := eventually_atTop.mp (Wage.pays_length hG A ht)
    filter_upwards [eventually_ge_atTop (m+1)] with i hi
    cases i with
    | zero => simp at hi
    | succ j =>
      have hr : 0 < ((C.S.block j).val:ℝ) := zero_lt_one.trans (block_one C j)
      exact (cheap C j).trans (Real.log_le_log hr (hm j (Nat.succ_le_succ_iff.mp hi)))
  obtain ⟨r,hr⟩ := H
  refine ⟨r+1+Nat.ceil δ,?_⟩
  filter_upwards [(Wage.log_tend hG A).eventually_ge_atTop 1,hA,hr] with i hi ha hv
  change 1 ≤ f i at hi
  change (A.params i).supportExponent ≤ (r:ℝ)*f i at hv
  change Real.log _ ≤ (↑(r+1+Nat.ceil δ):ℝ)*f i
  unfold market; rw [Real.log_mul (Real.exp_pos _).ne' (lt_of_lt_of_le zero_lt_one (column_one C i)).ne', Real.log_exp]; push_cast
  have hx : δ≤(Nat.ceil δ:ℝ)*f i := (Nat.le_ceil _).trans (le_mul_of_one_le_right (by positivity) hi)
  dsimp only [A] at ha hv; change Real.log (C.path.levels.params i).columns ≤ f i at ha
  linarith

/-- Two requisitions. Spend exp(B/64) for all-modes reset *including*
physical engineering and raw per-marker price. Also pay to CALL a normalized
local test with a pinned, reoriented output singleton. -/
structure Quotes (d : ℕ) : Prop where
  reach (k : ℕ) (E : ℝ) : 0<E → width C δ i k E * touch C d i * neighboring C i / width C δ (i+1) k E ≤
    Real.exp ((C.path.levels.clock.coverSize i:ℝ)/64)
  reverse (k : ℕ) (E : ℝ) : 0<E → width C δ (i+1) k E / (touch C d i * width C δ i k E) ≤ Real.exp ((C.path.levels.clock.coverSize i:ℝ)/512)


end YM.AnalyticNext.GridStop.Planning
