import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Clearance

/-!
# Return the cost to the SAME Gaussian

Applies at commit V (or any additional tested germ point with budgets
there). Majorant is taken on entire Z-law, using the on-chart inequality.
No overcount of sup/θ from other orientations. The chart scale of Fker
is present and is PAID by this change; `fare` doesn't disappear by
independence. Includes auxiliary powers for comparison estimates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Curtain Tariff Spot.Programme Spot Notice Moments
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

namespace Tariff
variable {ι α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] [DecidableEq β]
    (T : Tariff α β γ ι)

def impulse (α β γ ι : Type) [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] (k J : ℕ) : ℝ := Reading.Clearance.degrees k (Fintype.card α) (Fintype.card β) (Fintype.card γ)
  (Fintype.card ι) J

def radii (k J : ℕ) (z : Vec ι) : ℝ := impulse α β γ ι k J * (T.grow z)^4

def finalPower (k J i j : ℕ) (z : Vec ι) := T.codex z * (T.radii k J z)^i * (T.grow z)^j

def degreeTag (i j : ℕ) := T.orderPay * (4*i+j)
def sigmaRate (k J : ℕ) := impulse α β γ ι k J*T.ray^4
def outside (k J i j : ℕ) := T.salary * (T.sigmaRate k J)^i * T.ray^j

lemma beta_price (k J i j : ℕ) (z : Vec ι) : T.finalPower k J i j z=
    T.outside k J i j*slopeEnvelope T.seat T.capacity (T.degreeTag i j) z := by
  unfold finalPower outside sigmaRate codex radii grow slopeEnvelope degreeTag; ring

def universal (k J i j : ℕ) := T.outside k J i j * meter (Fintype.card ι) T.seat.card T.capacity (T.degreeTag i j)

lemma outside_nonneg (h : T.Lease) (k J i j : ℕ) : 0 ≤ T.outside k J i j := by
  have hx := h.solvent; have hp := zero_lt_one.trans_le h.high
  have ht : 0 < impulse α β γ ι k J := Reading.Clearance.degrees_pos ..
  unfold outside sigmaRate; positivity
lemma every_nonneg (h : T.Lease) (k J i j : ℕ) (z : Vec ι) : 0 ≤ T.finalPower k J i j z := by
  rw [T.beta_price]; exact mul_nonneg (T.outside_nonneg h ..) (slopeEnvelope_pos ..).le

@[fun_prop] lemma meter_meas (k J i j : ℕ) : Measurable (T.finalPower k J i j) := by
  unfold finalPower radii grow codex; apply Continuous.measurable; fun_prop
lemma spends [DecidableEq ι] (h : T.Lease) (k J i j : ℕ) {C : Next.SectorChange.Gaussian.Table ι} (hl : C.PosDef) (he : Peak C T.capacity) :
    Integrable (T.finalPower k J i j) (cloud C) ∧ (∫ z,T.finalPower k J i j z ∂cloud C) ≤ T.universal k J i j := by
  have hi : T.finalPower k J i j = fun z => _ := funext (T.beta_price k J i j)
  obtain ⟨hs,hg⟩ := Moments.purchased T.seat h.size hl he (T.degreeTag i j)
  rw [hi,integral_const_mul]; exact ⟨hs.const_mul _,mul_le_mul_of_nonneg_left hg (T.outside_nonneg h ..)⟩
end Tariff

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u : Spot d}
  {H R K α β γ : Type} [Fintype H] [Fintype R] [Fintype K] [DecidableEq H] [DecidableEq R]
  [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
  {X : Support c} {l : Viewport u X H R K} {D : u.Slices} {b : Finset ℕ} {q : Programme D b}
  {n : q.Run α β γ} {a : Notice l}

namespace Notice
variable (a : Notice l) (T : Tariff α β γ (Component G H R)) (k i j : ℕ) (r : ℝ)

-- Rates already include taxes, INCLUDING salary.
def reinforce (V : Config G c) (p : Reel G H R K) := a.strip r V p * T.finalPower k (Fintype.card H) i j (a.imprint V p)

lemma repaid (h : T.Lease) (hr : Ready d.chart d.g r) (V : Config G c) (hV : (a.C V).PosDef) (he : Peak (a.C V) T.capacity) :
    Integrable (a.reinforce T k i j r V) (pullLaw G H R K) ∧
      (∫ p,a.reinforce T k i j r V p∂pullLaw G H R K) ≤ T.universal k (Fintype.card H) i j := by
  let F : LinkArray G K→Coordinates G H R→ℝ := fun _ z => T.finalPower k (Fintype.card H) i j z
  have hl := spends T h k (Fintype.card H) i j hV he
  have ht := hl.1.comp_snd (piHaar G K)
  have hx := returns_cheaply d.chart d.g r (l.copy V) (a.C V) (piHaar G K) hr hV (a.tide V) (a.readable V) F
    ((T.meter_meas k (Fintype.card H) i j).comp measurable_snd) ht (fun x z => T.every_nonneg h ..)
  refine ⟨hx.1,hx.2.trans ?_⟩
  change Integrable (uncurry F) _ at ht
  rw [integral_prod _ ht]
  simpa [uncurry,F] using hl.2
end Notice
namespace Reading.Clearance

variable {B : Reading a n} {Ω : Set (Config G c)} {V : Config G c}
    {r t : ℝ} {T : Tariff α β γ (Component G H R)} {W : Directions G c → Prop} {k : ℕ}

omit [Fintype K] in
lemma cash (h : Clearance B t T V W k) (hr : Ready d.chart d.g r)
    (hV : Ω∈ nhds V) (hk : t<r) (hs : B.Shutter Ω t) (L : List (Directions G c)) (hl : L.length ≤ k)
    (hu : ∀i∈L,W i) (p : Reel G H R K) : ‖leftDerivs (fun V => B.endorsed r V p) L V‖ ≤
      a.reinforce T k L.length 0 r V p := by
  refine ((h.success hr hV hk hs p).price L hl hu).trans_eq ?_
  unfold Notice.reinforce Tariff.finalPower Tariff.radii impulse
  ring
end Reading.Clearance
end YM.AnalyticBridge.LocalGaussian
