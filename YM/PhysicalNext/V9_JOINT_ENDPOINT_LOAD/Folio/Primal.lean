import YM.AnalyticBridge.RESET_INCOME_PORT.Cohort
import YM.Extra.SOURCE_HISTORIES.Peel
import YM.Next.ROTATIONS
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Extension
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Sails
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Takings
import YM.Push.ABSOLUTE_SUMS.Fees


/-! # Whole first-address product costs at the physical JointLoad prices

Use `u_C`'s exponent with full dependency support, even if paying for the
leftDerivs at any point of that support. Same schedule & ranks as the shared
Lease (and the endorsed derivative budget there). Commission the FHtree-style
extra cover exponents and halo width/admissible rates before launch; NOT
asserting a ready calendar uses these widths if it hasn't bought the extra
time. The tree price for OTHER optional families and dependencies remains an
input elsewhere, similarly counting actual variants & attaching marks and
retaining seats/query contexts when dropping or restoring masks. No erasing
non-realizable visits in the hit test. The valuation is uniform in all
absolute positions, tags, Y, orientations and forest choices. The ADDRESS
set does *not* sum over those conditions, or use a different T or gauge on
each subfactor when taking a derivative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix Finset
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure Presented
open AnalyticBridge.LocalGaussian Spot Spot.Programme Notice Reading Tariff
open MeasureTheory SectorNext.Remainder Push.AbsoluteSums
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical

structure Aux where
  halo : ℕ
  power : ℕ  -- betaF power extra multiplier for these hits
  exponent : ℝ -- full exponent to ask for the hit
  broad : 40 ≤ halo

namespace Aux
variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {Q : Kiosk} {P : Teller G} (J : Aux)
abbrev radius (x : ℝ) := J.halo * radiusB x
def payto (G : Gauge) (P : Patch) (x : ℝ) := Scales.y G P.L x^(J.power:ℝ)
def due (Q : Kiosk) (x : ℝ) := rate (-(prize Q.v/2)) (radiusB x)
def asks (Q : Kiosk) (d : Desk G S) (w : Paper f → ℝ) :=
    Ac.Hit (spread S (J.radius d.betaHat)) (radiusB d.betaHat) (fun u => J.payto G S.patch d.betaHat * w u) J.exponent (due Q d.betaHat)

structure Basis (J : Aux) (Q : Kiosk) (d : Desk G S) (P : Teller G) (k : ℕ) : Prop where
  news : LocalNotice P d
  reaches : d.out.threshold = temp d.betaHat
  range : d.input.beta ≤ 2*Scales.y G S.patch.L d.betaHat
  outlet : 0<Scales.y G S.patch.L d.betaHat ∧ temp d.betaHat ≤ 2*fiery G d.betaHat S.patch.L
  reserve : 1 ≤ J.payto G S.patch d.betaHat ∧ ((radiusB d.betaHat+radiusB d.betaHat+1:ℕ):ℝ)^4 * due Q d.betaHat ≤ 1
  tertiary : J.asks Q d (audited Q.v d k (J.radius d.betaHat))
  primary : J.asks Q d (fun u => Real.sqrt (flame Q.v G S (J.radius d.betaHat) d.betaHat d.out k u))

lemma ceremony (v : Charges) (G : Gauge) (P : Patch) {L : ℝ} (hL : 0 ≤ L) (k : ℕ) : ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f),
    S.patch=P → Ac.Hit (spread S (J.radius x)) (radiusB x)
      (fun u=> J.payto G P x * (L * premiums v G x (home S) k (J.radius x) u)) J.exponent (rate (-(prize v/2)) (radiusB x)) := by
  have hp := prize_pos v
  let t x := rate (-(prize v/4)) (radiusB x)
  have he : Tendsto t atTop (𝓝 0) := SectorTools.PhysicalGaussianInsertion.Physical.error_limit _ (by positivity)
  have h1 : Tendsto (fun x=> L*t x) atTop (𝓝 0) := by simpa using he.const_mul L
  filter_upwards [takings v P G (max 0 J.exponent) k J.halo (le_max_left ..),
      Fees.route_tail_decay G P.L (by positivity : 0<prize v/4) (show 0<(J.power:ℝ)+1 by positivity), h1.eventually_le_const zero_lt_one,
      (Scales.year G P.L).eventually_ge_atTop 1] with x hx he1 h2 hw c f S hP z
  have hy : J.payto G P x * t x ≤ 1 := by
    have hr : 0 < Scales.y G P.L x := zero_lt_one.trans_le hw
    have hp' : J.payto G P x ≤ (Scales.y G P.L x)^((J.power:ℝ)+1) := Real.rpow_le_rpow_of_exponent_le hw (by linarith)
    have he : t x ≤ Real.exp (-(prize v/4)*Stores.till x) := Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (Nat.div_le_self ..)) (by linarith))
    unfold payto t
    exact (mul_le_mul hp' (he.trans he1) (rate_pos ..).le (Real.rpow_pos_of_pos hr _).le).trans (le_of_eq (by unfold Scales.y at hr ⊢; rw [Real.rpow_neg hr.le,mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne']))
  have hw' := zero_lt_one.trans_le hw
  have hZ := Real.rpow_nonneg hw'.le (J.power:ℝ)
  let M := J.payto G P x * L
  apply budget_loosen (C:= M * rate (-prize v) (radiusB x)) ?_ ?_
  swap
  · calc
      _ = (L*t x) * (J.payto G P x*t x) * rate (-(prize v/2)) (radiusB x) := by unfold t M rate; simp_rw [mul_assoc]; rw [← Real.exp_add,mul_left_comm (Real.exp _),← Real.exp_add]; ring_nf
      _ ≤ _ := mul_le_of_le_one_left (rate_pos ..).le (mul_le_one₀ h2 (mul_nonneg hZ (rate_pos ..).le) hy)
  apply budget_mono (budget_scale (show 0≤M from mul_nonneg hZ hL) (hx.test S hP z))
  · intro i; split; next => exact mul_nonneg (mul_nonneg hZ (mul_nonneg hL (premiums_nn ..))) (Real.exp_pos _).le
    next => exact le_rfl
  intro i; split
  next hi =>
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_max_right ..) (Nat.cast_nonneg _))) (premiums_nn ..)) (show 0≤M from mul_nonneg hZ hL))
    exact le_of_eq (by unfold M; ring)
  next he => rw [mul_zero]

lemma purchased (Q : Kiosk) (P : Teller G) (N : Patch) (Z : ChartRatio G) (χ : Chi) (r : ℝ) (power k : ℕ) : ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (d : Desk G S), S.patch=N → Calling P Z χ power r x d → Basis J Q d P k := by
  let m:= (power*k+1)*k
  have ht := (prize_pos Q.v); have hu := (tendsto_bill _ (show 0<prize Q.v/2 by positivity) 2 4).comp Work.E01.radiusB_tendsto
  filter_upwards [subscribe P N, outings G N, (Scales.year G N.L).eventually_ge_atTop 1,
      hu.eventually_le_const zero_lt_one, J.ceremony Q.v G N (by unfold commission; positivity : 0≤ commission G) (4*k),
      J.ceremony Q.v G N (pow_nonneg (by norm_num : 0≤(2:ℝ)) m) m] with x h₀ h₁ h₂ h₃ h₄ h₅ c f S d hS hd
  obtain ⟨hx,hQ,rfl,hβ,hy,hz,hχ,rfl,hD⟩ := hd
  refine ⟨h₀ S d.tube hQ hS,hD,hβ.2,hS ▸ h₁,⟨Real.one_le_rpow (hS ▸ h₂) (Nat.cast_nonneg _),?_⟩,
      ?_,?_⟩
  · apply Eq.trans_le ?_ h₃
    dsimp only [Function.comp_apply]; unfold due; push_cast; ring
  · unfold asks audited; rw [hS]; exact h₄ S hS
  unfold asks; simp_rw [flame, show ∀ i, Real.sqrt ((2^candles d.out k * premiums Q.v G d.betaHat (home S) (candles d.out k) (J.radius d.betaHat) i)^2)=(2^candles d.out k * premiums Q.v G d.betaHat (home S) (candles d.out k) (J.radius d.betaHat) i) from
    fun i => Real.sqrt_sq (mul_nonneg (by positivity) (premiums_nn ..)) ]
  rw [hS]; exact h₅ S hS
end Aux
end YM.PhysicalNext.JointLoad.Folio
