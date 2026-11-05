import YM.Next.RANK.Bought
import YM.Next.RANK.Station

/-!
# Normalized positions

Use E A angular detector positions in a centered link cell. Deterministic
right-closed rounding of *each coordinate*, never first testing continuum
jets. Keep coordinatewise separation by using a sufficiently deep station.
Space already at the middle cell so there really is a reflected margin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Station
open MeasureTheory Lattice Wilson RG Filter Set Extraction Cells
open scoped Topology BigOperators

variable {G : Gauge} (a : Levels G) (b : ℝ) (k : ℕ) {n : ℕ} (x : Points n)

def choose := Extraction.address (mag a b k)⁻¹ x

def key := Extraction.tag (a.S.a k) (choose a b k x)

def tested := (gap a b k)⁻¹ • key a b k x

lemma reading : tested a b k x=Extraction.tag (mag a b k)⁻¹ (Extraction.address (mag a b k)⁻¹ x) := by
  ext1 i; apply PiLp.ext; intro j
  change ((a.S.a k * mag a b k)⁻¹:ℝ)*(a.S.a k*↑(choose a b k x i j))=(mag a b k)⁻¹*↑(choose a b k x i j)
  have hm := mag_pos a b k; have hs := a.S.a_pos k; field_simp

lemma tuning {b : ℝ} (h : G.Simple) (hb : 0<b) : Tendsto (fun k => tested a b k x) atTop (𝓝 x) := by
  have hp := tendsto_inv_atTop_zero.comp (mag_rate a h hb)
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero (fun _ => dist_nonneg) (fun k => Eq.trans_le (congr_arg (fun y => dist y x) (reading a b k x)) (Extraction.approximate (inv_pos.mpr (mag_pos ..)) x)) ?_
  simpa only [mul_zero] using! hp.const_mul (4*n:ℝ)

lemma anchored : key a b k x = (gap a b k) • tested a b k x := by unfold tested; rw [smul_smul,mul_inv_cancel₀ (gap_pos ..).ne',one_smul]

/-- Keep a sizeable margin even relative to the middle cell. -/
structure Fit : Prop where
  usable : key a b k x ∈ YM.generic n
  deep (i j) : |key a b k x i j| ≤ a.S.a (middle a b k)/8

variable {a b k x}
lemma ready (h : G.Simple) (x : Points n) (hx : x∈ YM.generic n) (a : Levels G) (hb : 0<b) :
    ∀ᶠ k in atTop, Allowed a b k → Fit a b k x := by
  have hp := tuning a x h hb
  have ha : ∀ i : Fin n, ∀ j : Axis, ∀ᶠ k in atTop, 8*|tested a b k x i j| ≤ a.clock.monitor k ^ 2 := by
    intro i j
    have ht : Tendsto (fun k => 8*|tested a b k x i j|) atTop (𝓝 (8*|x i j|)) :=
      (show Continuous fun p : Points n => 8*|p i j| by fun_prop).continuousAt.tendsto.comp hp
    have he : Tendsto (fun k => a.clock.monitor k ^ (2:ℕ)) atTop atTop := by
      have he := mag_rate a h (show (0:ℝ)<2 by norm_num)
      refine he.congr fun i => Real.rpow_two _
    exact (ht.eventually (ge_mem_nhds (lt_add_of_pos_right (8*|x i j|) zero_lt_one))).mp ((he.eventually_ge_atTop _).mono fun _ h hx => le_trans hx h)
  filter_upwards [hp.eventually ((genericOpen n).mem_nhds hx), eventually_all.mpr (fun i => eventually_all.mpr (ha i))] with k hk hw he
  refine ⟨by rw [anchored]; exact Market.vision _ (gap_pos ..) _ hk,fun i j => ?_⟩
  rw [anchored]
  change |gap a b k * tested a b k x i j| ≤ _
  rw [abs_mul, abs_of_nonneg (gap_pos ..).le]
  have hx := mul_le_mul_of_nonneg_left (show 8*|tested a b k x i j| ≤ a.clock.monitor k ^ 2 from hw i j) (gap_pos a b k).le
  have hg := (le_div_iff₀ (a.S.a_pos k)).1 he.dilation
  unfold gap at *; linarith only [hx,hg]

lemma Fit.within (h : Fit a b k x) (i j) : |key a b k x i j| ≤ a.S.a (width a b k)*(2⁻¹ - 1/4) := by
  have hf := a.S.strictAnti.antitone (wider a b k)
  have hi := a.S.a_pos (middle a b k)
  linarith [h.deep i j]


end YM.Next.Rank.Station
