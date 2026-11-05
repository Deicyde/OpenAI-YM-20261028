import YM.Next.RANK.Tuning
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.Next.RANK.Tuning for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Station
open MeasureTheory Lattice Wilson RG Filter Set Extraction Cells
open scoped Topology BigOperators

variable {G : Gauge} (a : Levels G) (b : ℝ) (k : ℕ) {n : ℕ} (x : Points n)

/-- Keep a sizeable margin even relative to the middle cell. -/
structure FitSky : Prop where
  usable : key a b k x ∈ YM.generic n
  deep (i j) : |key a b k x i j| ≤ a.S.a (middleSky a b k)/8

variable {a b k x}
lemma readySky (h : G.Simple) (x : Points n) (hx : x∈ YM.generic n) (a : Levels G) (hb : 0<b) :
    ∀ᶠ k in atTop, AllowedSky a b k → FitSky a b k x := by
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

end YM.Next.Rank.Station
