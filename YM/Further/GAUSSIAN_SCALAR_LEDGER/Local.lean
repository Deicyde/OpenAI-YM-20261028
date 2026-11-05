import YM.Further.GAUSSIAN_SCALAR_LEDGER.Columns
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Inactive
import YM.Further.GAUSSIAN_SCALAR_LEDGER.LogWindow
import YM.Progress.STATIONARY_SCENES.Dispatch


set_option warningAsError false

/-!
# Fsct in terms of true principal windows, with per-coordinate local price

Actual logdet equalities incl **both** signs in paired windows. Prices
per key i (sum over complete color for site). e^{-fixed·window radius}
under exponential absolute row & column cost & uniform spectral input.
No assumption on seed separation for this bound beyond funding those
inputs. These are uniform local errors in the **scalar** price; no
claims of V derivatives or that exponentiating gives a summable list
of activities. Stencil of A itself as a function of geometry/history,
and upper range of windows, not purchased here. Keep every Π, E and S
entry's arguments if decomposing (including full reads for zeros).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function Filter Precision SectorNext.Vacuum Lattice Tree RG
open Round (rowRate)
open YM.Progress.StationaryScenes.Green
open MeasureTheory Set Wilson Pressure Push.SectorMeasure
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

private lemma line_amount {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Wall ι} {a b : ℝ}
    (h : A.IsHermitian) (ht : Numeric A a b) (ha : 0 < a) (hb : a≤b) (i : ι) :
    |Panel.priceLine A b i| ≤ Panel.amount a b := by
  let v := h.eigenvectorUnitary.val
  let w := fun k => v i k ^ 2
  have he : ∑ k, w k=1 := by
    have hh : v*vᴴ=1 := h.eigenvectorUnitary.prop.2
    simpa [w,Matrix.mul_apply,pow_two] using congr_arg (fun Q : Wall ι => Q i i) hh
  rw [Panel.priceLine,(Panel.balance _ h ht ha hb i).tsum_eq]
  rw [add_sub_cancel]
  apply le_trans (Finset.abs_sum_le_sum_abs ..)
  apply le_trans (b:=∑ k,w k* Panel.amount a b) _ (by rw [←Finset.sum_mul,he,one_mul])
  refine Finset.sum_le_sum fun k _ => ?_
  have hf (k) : 0 ≤ w k := sq_nonneg _
  change |w k * _| ≤ _
  rw [abs_mul,abs_of_nonneg (hf _)]
  apply mul_le_mul_of_nonneg_left _ (hf _)
  have hx := Panel.bill_quad h ht k
  apply abs_le.mpr
  unfold Panel.amount
  constructor
  · linarith only [neg_le_abs (Real.log a), Real.log_le_log ha hx.1,abs_nonneg (Real.log b)]
  linarith only [abs_nonneg (Real.log a),Real.log_le_log (ha.trans_le hx.1) hx.2, le_abs_self (Real.log b)]

/- Price error independent of period, cutoff & tag **given** constants
on tested matrices. Number of keys not included: log pressure remains
extensive. -/
def Expense.fog (p : Expense) (r : ℝ) :=
  p.payment * p.windowCost r / (1-p.windowCost r) + p.correctionCost r / (1-p.correctionCost r)/2
lemma Expense.fog_bound (p : Expense) {r : ℝ} (ht : Timing p r) :
    p.fog r ≤ (2*p.payment*p.windowCost r+p.correctionCost r) := by
  have he := ht.misses
  have hh := ht.small
  have h (x : ℝ) (hx : x < 1/2) (b : ℝ) (hb : 0 ≤ b) : b/(1-x) ≤ 2*b := by
    rw [div_le_iff₀ (by linarith : 0<1-x)]; nlinarith
  unfold fog
  have hb := h _ he _ (mul_nonneg p.payment_pos.le (p.window_pos r).le)
  have hw := h _ hh _ (p.correction_pos r).le
  linarith


variable {c f : Side} {S : StepData c f} {F : Forest S.ratio} {G : Gauge} {O : ChartRatio G}
    {rooms : Type*} [Fintype rooms]

namespace Fiber
variable (v : Fiber F O rooms) (p : Expense) (Z : Lens (Key F G)) (B0 : Wall (Key F G))

def viewLens (Y : Frozen v.H G) := RawPrice.field Z (v.sigma Y)

def bLift (Y : Frozen v.H G) : VV (Key F G) := spreadBits v.H (linearCost (v.D Y) (v.b0 Y))

def viewMean (Y : Frozen v.H G) := RawPrice.meanAt Z (v.sigma Y) (v.bLift Y)

/-- Choose exactly the principal field and local mean on these inputs.
Doesn't modify the chart openings, rows, or F0's. -/
def screen : Fiber F O rooms :=
  { v with C := fun Y => blankOut v.H (v.viewLens Z Y)
           μ := fun Y => viewBits v.H (v.viewMean Z Y) }

variable {n : Side} {y : Key F G → Site n} {r : ℝ}

lemma agrees (Y : Frozen v.H G) (h : RawPrice p y (v.sigma Y)) :
    (v.screen Z).complete Y = v.viewLens Z Y ∧ (v.screen Z).eps Y=RawPrice.tear Z (v.sigma Y) ∧
    spreadBits v.H ((v.screen Z).μ Y) = v.viewMean Z Y := by
  have he : (v.screen Z).complete Y = v.viewLens Z Y := Z.muted v.H _ (h.paid p)
  rw [eps,he]; refine ⟨rfl,rfl,?_⟩
  exact sees_mean v.H (precision (v.D Y)) Z (linearCost (v.D Y) (v.b0 Y)) (h.paid p)

lemma screened (hp : p.low ≤ p.high) (h : ∀ Y, RawPrice p y (v.sigma Y))
    (hr : Z.Outside y r) (ht : Timing p r) :
    (v.screen Z).Rates p.low p.high (p.correctionCost r) := by
  refine ⟨p.low_pos,hp,(p.correction_pos _).le, ht.small.trans (by norm_num),fun Y => (h Y).positive,
    fun Y => ?_, fun Y => ?_⟩
  · rw [(v.agrees p Z _ (h Y)).2.1]
    exact (Double.into_rate ((h Y).frays Z p hr) p.margin_pos.le).1
  exact Matrix.IsHermitian.submatrix (RawPrice.field_transpose ..) _

def nearby (Y : Frozen v.H G) (i : Key F G) :=
  -(Z.localLine (v.sigma Y) p.high i-Z.localLine B0 p.high i)/2

def trailPrice (Y : Frozen v.H G) (i : Key F G) :=
  -((∑' n, ∫ u in Ioi (0:ℝ), Z.beadPulse (v.sigma Y) n i i u) -
    (∑' n, ∫ u in Ioi (0:ℝ), Z.beadPulse B0 n i i u))/2 +
    Round.onLine (v.eps Y) i/2

lemma localized {η L q} (ha : η=p.low) (hL : L=p.high) (Y : Frozen v.H G)
    (ht : v.Rates η L q) (h : RawPrice p y (v.sigma Y)) (hh : RawPrice p y B0)
    (hr : Z.Outside y r) (hm : Timing p r) (β : ℝ) :
    v.chargeOut B0 β Y = -∑ _ ∈ v.H,Real.log (gaussLink O β) +
      ∑ i,(v.nearby p Z B0 Y i + v.trailPrice Z B0 Y i) := by
  rw [chargeOut, log_form_anchor F O β _ _ _ _ hh.hermitian h.hermitian hh.positive h.positive
    p.low_pos (show p.low ≤ p.high from ha ▸ hL ▸ ht.mind) ht.low ht.high (ht.rate Y)]
  congr 1; apply Finset.sum_congr rfl; intro i _
  rw [h.anchored Z p hr hm,hh.anchored Z p hr hm]; unfold nearby trailPrice eps; ring

/-- Together Echs into the determinant correction of Fsct (Frco nonconstant ratios separate). Usable even with a previously
produced C which agrees with the window field on completion.
Per-anchor uniform local error, true infinite sums. For individual chain-series
norm summability see `RawPrice.tails`, `Round.lineSummable` and Entries.
-/
theorem in_book (hp : p.low≤p.high) (h : ∀ Y, RawPrice p y (v.sigma Y)) (hh : RawPrice p y B0)
    (hr : Z.Outside y r) (hm : Timing p r) (hc : ∀ Y, v.C Y=(v.screen Z).C Y) (Y : Frozen v.H G) (β : ℝ) :
    v.chargeOut B0 β Y = -∑ _ ∈ v.H,Real.log (gaussLink O β) +
      ∑ i,(v.nearby p Z B0 Y i + v.trailPrice Z B0 Y i) ∧
      ∀ i, |v.nearby p Z B0 Y i| ≤ Panel.amount p.low p.high ∧
        |v.trailPrice Z B0 Y i| ≤ p.fog r := by
  have ht := v.screened p Z hp h hr hm
  have hw Y : v.eps Y=(v.screen Z).eps Y := by unfold eps complete; rw [hc Y]; rfl
  have hR : v.Rates p.low p.high (p.correctionCost r) := ⟨ht.1,ht.2,ht.3,ht.4,
    ht.5,fun i => by rw [hw]; exact ht.rate i, fun i => by rw [hc]; exact ht.symm i⟩
  refine ⟨localized v p Z B0 rfl rfl _ hR (h Y) hh hr hm β, fun i => ⟨?_,?_⟩⟩
  · have he (X : Wall (Key F G)) (H : RawPrice p y X) : |Z.localLine X p.high i| ≤ Panel.amount p.low p.high :=
      line_amount (Matrix.IsHermitian.submatrix H.hermitian _) (Z.numerate X _ _ H.positive i)
        p.low_pos hp (Z.center i)
    unfold nearby; rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith [he _ (h Y), he _ hh,
      abs_sub (Z.localLine (v.sigma Y) p.high i) (Z.localLine B0 p.high i)]
  have hz := ((h Y).first_bound Z p hr hm i)
  have he := hh.first_bound Z p hr hm i
  have hg := tail_ripple (v.eps Y) (hR.rate Y) hR.low hR.high i i 0
  simp only [Nat.add_zero,Nat.zero_add,pow_one] at hg
  have hS : |Round.onLine (v.eps Y) i| ≤ p.correctionCost r/(1-p.correctionCost r) :=
    (norm_tsum_le_tsum_norm hg.1.norm).trans hg.2
  unfold trailPrice
  rw [((h Y).chains Z p hr hm i).tsum_eq,(hh.chains Z p hr hm i).tsum_eq]
  apply (abs_add_le ..).trans; rw [abs_div,abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  unfold Expense.fog
  linarith only [hz,he,hS,abs_sub (Panel.priceLine (v.sigma Y) p.high i-Z.localLine (v.sigma Y) p.high i)
    (Panel.priceLine B0 p.high i-Z.localLine B0 p.high i)]
end Fiber

/-- A `Scanner` which uses the actual prescribed windows. Delay from
`Expense` after paying parameters; works identically with arbitrary
paired orientations provided on these ports. No Loop/ζ locality or
selection prerequisites about the POLICIES on v,Z,y here; only scalar
matrix bounds and the matrices of the value version. -/
theorem activeScanner (Z : Lens (Key F G)) (B : Wall (Key F G)) (p : Expense) {n : Side}
    {y : Key F G → Site n} {r x W : ℝ} (d : Allocation G S x W)
    (v : Stores S → S.Choices → Config G c → Fiber F O rooms) (hi : p.low ≤ p.high)
    (h : RawPrice p y B) (hu : ∀ P k V Y, RawPrice p y ((v P k V).sigma Y))
    (ht : Timing p r) (hz : Z.Outside y r) (he : ∀ P k V, Opened O (v P k V).veil d P k V) :
    Scanner B d (fun P k V => (v P k V).screen Z) p.low p.high (p.correctionCost r) :=
  ⟨fun P k V => he P k V, fun P k V => (v P k V).screened p Z hi (hu P k V) hz ht,
    h.hermitian,h.positive,p.low_pos⟩

end YM.Further.GaussianScalar
