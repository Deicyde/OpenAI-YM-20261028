import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.WindowLog
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bore
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ledger
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical


/-!
# Actual log-term receipts can be issued for the same Teller call

Same panels, same completed key, same tag capabilities. No dependence
on stationary data at other N. Buy at all ASSEMBLED V with correct flags
(*not* inferring a uniform upper from Hector for a deliberately
mismatched A). Also give all real costs of Fsct scalar local frozen
letters from same ChartRatio and band, for use separately from common
scalar and determinant correction. Actual g=β^(-1/2) may differ from
Scales.g from the same call's x. Don't substitute one for the other.
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Scales Finset Rows Wisps Schur Next.SectorChange.Completion Matrix
open scoped YM.Next.SectorChange.Completion ComplexOrder Topology

variable {c f : Side} {G : Gauge} {S : StepData c f}

/-- Sufficient pair pricing values. -/
def granting (P : Teller G) (Λ : Patch) (μ L x : ℝ) :=
    0 < μ ∧ μ≤1 ∧ 1≤L ∧ 120≤ radiusB x ∧ 0<x ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=Λ → 100*(1+radiusB x)≤c.val → P.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices), A.flags=RG.flags (temp x) V →
    Numeric (witnessGram T V x k A F) μ L ∧ Numeric (witnessGram T 1 x k (noHoles S) F) μ L ∧
    (fog A F T x V k).PosDef ∧ (gram T x V k (shots S x) A F).PosDef ∧ (Native.kinetic T F k x).PosDef





section currency
variable (Z : ChartRatio G)

def logFlat := (Fintype.card G.ColorIndex:ℝ) /2 * Real.log (2*Real.pi) + Real.log Z.scale

def logCash := |logFlat Z| + (Fintype.card G.ColorIndex:ℝ) * (1+Real.log 2)

lemma spare_formula {β : ℝ} (hp : 0<Z.scale) (h : 0<β) :
    Real.log (spare Z β)= logFlat Z - (Fintype.card G.ColorIndex:ℝ)/2 * Real.log β := by
  have he := coupling_pos h
  rw [spare,Real.log_mul (by have ht:=Real.pi_pos; positivity) hp.ne',Real.log_pow,Real.log_sqrt (by have ht:=Real.pi_pos; positivity),
    Real.log_mul (by have ht:=Real.pi_pos; positivity) (pow_pos he 2).ne',Real.log_pow,coupling,Real.log_inv,
    Real.log_sqrt h.le]
  unfold logFlat; ring

lemma logCash_nonneg : 0 ≤ logCash Z := by
  have he := Real.log_nonneg (show (1:ℝ)≤2 by norm_num)
  unfold logCash; positivity

lemma price_spare {β y : ℝ} (he : 0<Z.scale) (h : 1≤y) (hβ : β∈Set.Icc (y/2) (2*y)) :
    |Real.log (spare Z β)| ≤ logCash Z * (1+Real.log y) := by
  have ht : 0 < y/2 := by linarith
  obtain ⟨hb,hB⟩ := hβ
  have Hβ : 0<β := ht.trans_le hb
  have hl (i) (hi) := Real.log_nonneg (show 1 ≤ i from hi)
  have hv : 0≤Real.log y := hl y h
  have hi := hl 2 (by norm_num)
  have hm : |Real.log β| ≤ Real.log 2 + Real.log y := by
    rw [abs_le]; constructor
    · refine le_trans (b:= Real.log (y/2)) ?_ (Real.log_le_log ht hb)
      rw [Real.log_div (by linarith) (by norm_num)]; linarith
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log Hβ hB
  let C : ℝ := Fintype.card G.ColorIndex
  have hc : 0 ≤ C := Nat.cast_nonneg _
  rw [spare_formula Z he Hβ]
  refine (abs_sub ..).trans ?_
  rw [abs_mul,abs_of_nonneg (show 0≤C/2 from by positivity)]; unfold logCash
  change _ + C / 2 * _ ≤ (|logFlat Z|+C*(1+Real.log 2)) * (1+Real.log y)
  apply (add_le_add_right (mul_le_mul_of_nonneg_left hm (by positivity : 0≤C/2)) _).trans
  have hg := abs_nonneg (logFlat Z)
  nlinarith [mul_nonneg hg hv,mul_nonneg (mul_nonneg hc hi) hv, mul_nonneg hc hi,mul_nonneg hc hv]

end currency
end YM.AnalyticBridge.Annulus1AD
