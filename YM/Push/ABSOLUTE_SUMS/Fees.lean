import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Next.FLUCTUATIONS.Scales
import YM.Push.ABSOLUTE_SUMS.Delay
import YM.Push.ABSOLUTE_SUMS.Path
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04


/-!
# Numerical costs for the support/hit estimates

Gates for the estimates of THIS module.  ageom etc. Separates
pre-L price requirements for support reserve and post-L fixed-delay
polynomial losses. Actual dynamics estimates still have to *earn*
vertex prices, INCLUDING under successive step applications. In
particular no claim of support or path width maintenance under RG.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Fees
open Filter Lattice RG Pressure Footprint
open scoped BigOperators Topology

/-- Pre-L exponent fit. -/
lemma exponent (l : ℕ) {A ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hA : 2*ε < A) :
    ∃ n : ℕ, ∀ (c f : Side) (p : Ratio c f), n ≤ p.count.val → reserve A a (conversion p l) ε := by
  have hz : 0 < A-2*ε := by linarith
  obtain ⟨n,hn⟩ := exists_nat_gt ((10*preCost l)*a/(A-2*ε))
  refine ⟨n,fun c f p he => ⟨ha,hε,?_⟩⟩
  have hl : (n:ℝ) ≤ p.count.val := by exact_mod_cast he
  have hp : 0 < (p.count.val:ℝ) := by positivity
  have hh := (div_le_iff₀ hz).mp (hn.le.trans hl)
  unfold conversion; field_simp; linarith

variable (G : Gauge) (L : Side)

lemma horizons (l : ℕ) {σ a ε : ℝ} (he : 0 < ε) (ha : 0 ≤ a) (hs : 2*ε < σ) :
    ∀ᶠ x : ℝ in atTop, let B := radiusB x
    0 < B ∧ radiusB (betaF G x L) ≤ 2*B ∧
    ∀ (c f : Side) (p : Ratio c f), p.count=L → reserve σ a (Paths.legFee p l B) ε := by
  have h1 : Tendsto (fun x : ℝ => (radiusB x:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
  let k := G.slopeConstant*Real.log (L.val:ℝ)
  let A := a*(10*preCost l/(L.val:ℝ))
  filter_upwards [Stock.stepsize k, Work.E01.radiusB_tendsto.eventually_ge_atTop 1,
    h1.eventually_ge_atTop (A/(σ-2*ε))] with x hx ht he'
  intro B
  change radiusB (betaF G x L)^2 ≤ 2*B^2 at hx
  refine ⟨ht,(by nlinarith),fun c f p hp => ⟨ha,he,?_⟩⟩
  have heB : (0:ℝ)<B := by exact_mod_cast (show 0 < B from ht)
  have h := (div_le_iff₀ (sub_pos.mpr hs)).mp he'
  change A ≤ (B:ℝ)*(σ-2*ε) at h
  unfold Paths.legFee conversion
  rw [hp,← mul_div_assoc]; change A/(B:ℝ) + _ ≤ _
  have hB := (div_le_iff₀ heB).2 (show A ≤ (σ-2*ε)*(B:ℝ) by simpa only [mul_comm] using h)
  linarith

/-- Any post-L fixed-polynomial overhead of the B/P type is
sub-power of betaF. -/
lemma growth {r D : ℝ} (hr : 0 < r) (hD : 0 ≤ D) (z : ℝ) (d : ℕ) :
    ∀ᶠ x : ℝ in atTop, D * Delay.bill G L x ^ d * Delay.fineMonitor G L x ^ z ≤ betaF G x L ^ r := by
  filter_upwards [Delay.monitor_pays G L d hD (show (0:ℝ)<1 by norm_num), (Work.E09.betaF_growth G L).eventually
    (Vac.Numbers.cost (1+z) r hr)] with x hx hh
  let P := Delay.fineMonitor G L x
  have hp : 0 < P := Delay.monitor_pos ..
  apply le_trans (mul_le_mul_of_nonneg_right hx (Real.rpow_pos_of_pos hp z).le)
  change P ^ (1:ℝ) * P ^ z ≤ _
  rw [← Real.rpow_add hp]; exact hh

-- Two exemptions used for optional costs, charges explicitly
lemma hat_decay {a z : ℝ} (ha : 0 < a) (hz : 0 < z) {N : ℝ} (hn : 0 < N) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-a*(Delay.fineMonitor G L x)^z) ≤ betaF G x L ^ (-N) := by
  filter_upwards [Delay.monitor_pays G L 1 (show 0 ≤ N/a by positivity) hz,
    Delay.shift_pos G L] with x hx he
  rw [Real.rpow_def_of_pos he]; apply Real.exp_monotone
  have h : Real.log (betaF G x L) ≤ Delay.bill G L x := by
    unfold Delay.bill; have he := Nat.cast_nonneg (α:=ℝ) (radiusB x)
    nlinarith [sq_nonneg (Real.log (betaF G x L)-1/2)]
  rw [pow_one] at hx; field_simp at hx; linarith [mul_le_mul_of_nonneg_right h hn.le]

lemma route_tail_decay {a : ℝ} (ha : 0 < a) {N : ℝ} (hn : 0 < N) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-a*Stores.till x) ≤ betaF G x L ^ (-N) := by
  filter_upwards [Next.Fluctuations.tail_delay G L (a/N) (by positivity),Delay.shift_pos G L]
    with x hx he
  rw [Real.rpow_neg he.le]
  calc
    _ = (Real.exp (-(a/N)*Stores.till x))^N := by
      rw [← Real.exp_mul]; field_simp
    _ ≤ ((betaF G x L)⁻¹)^N := Real.rpow_le_rpow (Real.exp_pos _).le hx hn.le
    _ = _ := by rw [Real.inv_rpow he.le]




end YM.Push.AbsoluteSums.Fees
