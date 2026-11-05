import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.Push.ABSOLUTE_SUMS.Fees

/-!
# Wages on the actual heat band

Keep x the enclosing hat. No assumption of pricing at an unrelated
reset. Provides primitive use in BOTH per-output and per-component scales;
exponential wages for seed are VERY different from power of the group
threshold. Visits even when charged post-L ensure multiplicities everywhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Wages
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates Aff Aff.Mint
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge}

-- hypoth stage interval (even convenience OnBand deliberately even wider than band); use exact R range to derive.
def OnBand (G : Gauge) (D : Patch) (x β : ℝ) := betaF G x D.L/4 ≤ β ∧ β ≤ 4*betaF G x D.L
def power (β : ℝ) : ℝ := (Real.sqrt β)⁻¹

def sLink (G : Gauge) (N : ChartRatio G) (β : ℝ) := (Centered.unitVolume*power β)^(Fintype.card G.ColorIndex)*N.scale

abbrev tab (G : Gauge) (D : Patch) (x : ℝ) := Delay.bill G D.L x
abbrev starCharge (G : Gauge) (D : Patch) (x : ℝ) := Delay.fineMonitor G D.L x
lemma sLink_pos (G : Gauge) (N : ChartRatio G) (β : ℝ) (he : LocalRatio N) (hβ : 0<β) : 0<sLink G N β := by
  unfold sLink power; have ht := he.scale; have hx := Centered.unit_pos; positivity

lemma bump (G : Gauge) (D : Patch) (x : ℝ) (p : ℕ) : pieces x p ≤ tab G D x^p := by
  unfold pieces; apply pow_le_pow_left₀ (by positivity)
  unfold tab Delay.bill; linarith [sq_nonneg (Real.log (betaF G x D.L))]
lemma tab_cap (G : Gauge) (D : Patch) (p : ℕ) : ∀ᶠ x : ℝ in atTop, pieces x p ≤ tab G D x^p :=
  Eventually.of_forall fun x => bump G D x p

lemma paid (G : Gauge) (D : Patch) (C : ℝ) (p q : ℕ) (h : p<q) : ∀ᶠ x : ℝ in atTop,
    C*tab G D x^p ≤ tab G D x^q := by
  have ht : Tendsto (fun x : ℝ => (radiusB x:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
  filter_upwards [ht.eventually_ge_atTop C, tab_cap G D 1] with x hx hv
  unfold pieces at hv; rw [pow_one,pow_one] at hv
  have he := Delay.bill_ge G D.L x
  calc
    _ ≤ tab G D x^ (p+1) := by rw [pow_succ']; exact mul_le_mul_of_nonneg_right (hx.trans hv) (pow_nonneg (zero_le_one.trans he) _)
    _ ≤ _ := pow_le_pow_right₀ he h

lemma scaled (G : Gauge) (x : ℝ) (L : Side) (hx : 0<betaF G x L) : betaF G x L * (fiery G x L)^2 = (Delay.fineMonitor G L x)^2 := by
  have h := Real.sqrt_pos.mpr hx
  unfold fiery temp Delay.fineMonitor Vac.Numbers.P
  field_simp; rw [Real.sq_sqrt hx.le]

-- Utility: ANY fixed polynomial powers paid by t (or excess power over β t²).
lemma stipend (G : Gauge) (D : Patch) (k p : ℕ) (C : ℝ) (hp : 0≤C) {e : ℝ} (he : e<1/2) :
    ∀ᶠ x : ℝ in atTop, C * tab G D x ^ p * starCharge G D x^k * fiery G x D.L ≤
      betaF G x D.L^(-e : ℝ) := by
  filter_upwards [Fees.growth G D.L (show 0 < 1/2-e by linarith) hp (k+1:ℕ) p,
    Delay.shift_pos G D.L] with x hx hv
  let B := betaF G x D.L; let P := starCharge G D x
  have hb : 0 < B := hv
  calc
    _ = (C*tab G D x^p*P^((k+1:ℕ):ℝ))*(Real.sqrt B)⁻¹ := by
      rw [Real.rpow_natCast]; unfold P B starCharge Delay.fineMonitor Vac.Numbers.P fiery temp; ring
    _ ≤ B^(1/2-e)*(Real.sqrt B)⁻¹ := mul_le_mul_of_nonneg_right hx (by positivity)
    _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hb.le, ← Real.rpow_add hb]; congr 1; ring

lemma burn_card (G : Gauge) (D : Patch) (C : ℝ) (hC : 0 ≤ C) (p : ℕ) {e : ℝ} (he : e<1/2) : ∀ᶠ x : ℝ in atTop,
    C*(betaF G x D.L)*allowance G D x 3 p ≤ betaF G x D.L ^ (-e:ℝ) := by
  filter_upwards [stipend G D 2 p C hC he, Delay.shift_pos G D.L] with x hp hv
  let t := fiery G x D.L; have ht : 0≤t := temp_nonneg _
  have hq : 0≤starCharge G D x := (Delay.monitor_pos ..).le
  calc
    _ = C*pieces x p*(starCharge G D x)^2*t := by
      unfold allowance starCharge; rw [← scaled G x D.L hv]; unfold t; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (bump G D x p) hC) (sq_nonneg (starCharge ..))) ht).trans hp


end YM.AnalyticNext.ConnectedActivity.Wages
