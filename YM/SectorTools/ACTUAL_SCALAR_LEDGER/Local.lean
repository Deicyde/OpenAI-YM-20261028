import YM.Next.MAXWELL.Det
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix


set_option autoImplicit false
set_option warningAsError false
set_option synthInstance.maxSize 1024

/-!
# The value entries of the physical Ledger; Quote.Pays adapter

Conditional low-level interface from window/gap and intact charter receipts (produced
together before Bar in later module). First forecast *only* the two logs from their exact
principal matrices: one with windows on the full matched precision and blank sector,
the other with the same endpoints C / ordered residual. No flag differentiation or
post-reset estimate. Frame-local approximation error VALUE per key, total has native
link and color dimensions, NOT period-independent. Uses nat-floor coarse range, not
charging smallness retroactively on an arbitrary `Cosmos` alone.
-/
noncomputable section
namespace YM.SectorTools.ActualScalar
open Function Filter Set MeasureTheory Matrix RG Wilson Lattice Pressure Pressure.Stores Precision Tree Push.SectorMeasure
  Next.SectorChange Further GaussianScalar AnalyticBridge.ResetIncome SectorNext.Vacuum
open AnalyticBridge (GaussianFieldAlignment.Rates GaussianFieldAlignment.Ready)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (e : Plate G S) (v : AnalyticBridge.GaussianFieldAlignment.Rates)

structure Bought (e : Plate G S) (v : AnalyticBridge.GaussianFieldAlignment.Rates) : Prop where
  doors : Doors e
  localH : LocalRatio e.chart
  branches : S.patch.Branches S.kernel G
  standing A k V : e.matched A V → Next.SectorChange.Standing (F:=e.forest) (A:=A) e.book e.chart e.d k V
  sound A k V : e.matched A V ∨ V=1 → AnalyticBridge.GaussianFieldAlignment.Ready A e.forest e.x e.tube k V v.s v.η v.C v.D
  timed : Timing (expense G S.patch.L v) (rangeSize e.x)

namespace Bought
variable (he : Bought e v)
include he
local notation "p" => expense G S.patch.L v
variable {v e}
lemma tall : 120 ≤ radiusB e.x := Nat.le_trans (by decide : 120 ≤ 200) (he.sound noHole e.tag 1 (Or.inr rfl)).side

def lens := frame e he.tall

lemma sees (A : Stores S) (k : S.Choices) (V : Config G c) :
    AnalyticBridge.GaussianFieldAlignment.Ready A e.forest e.x e.tube k (supported e A V) v.s v.η v.C v.D :=
  he.sound A k _ <| by unfold supported; split <;> simp [*]

lemma tables (A : Stores S) (k : S.Choices) (V : Config G c) (Y : GaussianScalar.Frozen (held e A) G) :
    RawPrice p (distance e) ((sheets e he.doors A k V).sigma Y) := precision_price _ _ _ _ _ _ _ (he.sees A k V)
lemma flat : RawPrice p (distance e) e.Flat := by
  rw [← flat_price_eq e he.doors he.branches]; exact precision_price _ _ _ _ _ _ _ (he.sound noHole _ _ (Or.inr rfl))

lemma scanner : Scanner e.Flat e.book (sheets e he.doors) (p).low (p).high ((p).correctionCost (rangeSize e.x)) := by
  have hh A k V : Opened e.chart ((sheets e he.doors A k V).veil) e.book A k V := opened _ _ he.doors he.localH he.branches _ _ (he.standing A k V)
  have hx := activeScanner he.lens e.Flat p e.book (sheets e he.doors) (hi ..) he.flat he.tables he.timed (away e he.tall) hh
  have hs A k V : ((sheets e he.doors A k V).screen he.lens) = sheets e he.doors A k V := screened_eq _ he.doors _ _ _ he.tall v.η_pos (he.sees A k V).solvent
  simpa only [hs] using hx

lemma matched_log (A : Stores S) (k : S.Choices) (V : Config G c) (hv : e.matched A V)
    (Y : GaussianScalar.Frozen (held e A) G) :
    let W := page e he.doors A k V
    Round.traceLog (W.eps Y) = Real.log (1+(e.Gram A V k * e.Cov A V k - 1)).det := by
  have h := he.scanner.matrixRule A k V
  rw [opens_at_match _ _ _ _ _ hv] at h
  intro W; rw [(W.rates_trace h Y).2.1,(eps_price e he.doors A k V Y).2.2]
end Bought

lemma spare_eq (Z : ChartRatio G) (β : ℝ) (h : 0<β) : spare Z β=gaussLink Z β := by
  unfold Next.SectorChange.spare gaussLink
  rw [show coupling β ^ 2=β⁻¹ from (Fiber.spread_beta _ h).2, ← div_eq_mul_inv, Real.sqrt_eq_rpow,
      ← Real.rpow_mul_natCast (by positivity)]
  simp only [Gauge.Color,finrank_euclideanSpace]; congr 2; ring

lemma cost_eq (he : Bought e v) (R : Rep G f) (hr : 0<R.beta) (A : Stores S) (k : S.Choices) (V : Config G c) (hv : e.matched A V)
    (Y : GaussianScalar.Frozen (held e A) G) :
    e.cost R A V k = (page e he.doors A k V).chargeOut e.Flat R.beta Y := by
  unfold Plate.cost Fiber.chargeOut residualLog
  rw [← Fiber.eps, (eps_price ..).1, he.matched_log A k V hv Y,spare_eq e.chart _ hr]
  rw [← Fintype.card_congr (heldEquiv e A),Fintype.card_coe]; change _ = -(↑(held e A).card : ℝ)*_ - _/_ + _/_; ring

namespace Bought
variable (he : Bought e v)
include he
local notation "p" => expense G S.patch.L v
variable (R : Rep G f) (hr : 0<R.beta) (A : Stores S) (k : S.Choices) (V : Config G c) (Y : GaussianScalar.Frozen (held e A) G)
variable {e v}

include hr in
lemma windows (hv : e.matched A V) :
    let W := page e he.doors A k V
    e.cost R A V k = -∑ _ ∈ held e A,Real.log (gaussLink e.chart R.beta) +
      ∑ i,(W.nearby p he.lens e.Flat Y i + W.trailPrice he.lens e.Flat Y i) ∧
    (∀ i, |W.nearby p he.lens e.Flat Y i| ≤ Panel.amount (p).low (p).high ∧ |W.trailPrice he.lens e.Flat Y i| ≤ (p).fog (rangeSize e.x)) ∧
      |∑ i, W.trailPrice he.lens e.Flat Y i| ≤ Fintype.card (Key e.forest G)*(p).fog (rangeSize e.x) := by
  intro W
  have ht := he.sound A k V (Or.inl hv)
  have hh Y : RawPrice p (distance e) (W.sigma Y) := precision_price _ _ _ _ _ _ _ ht
  have he' y : W.C y=(W.screen he.lens).C y := C_eq _ _ _ _ _ _ _ v.η_pos ht.solvent
  obtain ⟨h1,h2⟩ := W.in_book p he.lens e.Flat (hi ..) hh he.flat (away e he.tall) he.timed he' Y R.beta
  rw [cost_eq _ v he R hr A k V hv Y]; exact ⟨h1,h2,(Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) fun i _ => (h2 i).2)⟩






end Bought
end YM.SectorTools.ActualScalar
