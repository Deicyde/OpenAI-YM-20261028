import YM.Push.RELAY_DIFFERENCE.Birth
import YM.Push.RELAY_DIFFERENCE.TwoSided


/-!
# Sufficient anticipatable charges for particular comparison exponents

Choose an inverse-hat power for `Prices.coin`, so marker radii can
expose the price of the singleton + the power, and use schedule for
the support reserve / radius-shrinkage in each mixed local output.
Prove one numeric compatibility result (,
156xx). Suppose the raw *bill i* (e.g. L_i^D times post-L factors, in
this version) also pays within a fixed hat power. That's a scale input
for THIS P only, not claiming a bound if post-block tariffs exceed it
(scheduled comparisons may prefer smaller P.reserve across a transition;
need a different proof in that case).

This doesn't select a calendar. The pre-L/exponent charges here remain
inputs on THIS clock. In particular, logCost alone (the stock receipt)
is NOT being used as a pre-L grant to burn the real derivative prices
unspecified after each step. Use with explicit reservation `preloaded`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Marker Overlay Stock Bid Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {C : Family G} {F : Trial C} {f : Extraction.Order} {P : Prices}

lemma local_price {G : Gauge} (H : Levels G) (i : ℕ) :
    let X := H.params (i+1)
    X.columns ≤ (H.S.block i).val ∧ X.supportExponent ≤ (H.S.block i).val := by
  intro X
  let L : ℝ := (H.S.block i).val
  let y : ℝ := 1+X.paths+X.width⁻¹+X.columns+X.clip.relaxation+X.supportExponent
  have he : 0 < Real.log L := Real.log_pos (by
    have hh : (3:ℝ) ≤ L := by unfold L; exact_mod_cast H.S.block_large i
    linarith)
  have hc : Real.log y ≤ Real.log L := by
    let j := (H.clock.J (i+1) : ℝ)
    have hz : 1 ≤ j := by
      have ht := H.clock.adm (i+1)
      unfold j
      exact_mod_cast (show 1 ≤ H.clock.J (i+1) from Nat.le_trans (by decide) ht)
    exact (div_le_one he).mp (le_trans (show Real.log y / Real.log L ≤ (j^2)⁻¹ from H.fits.logCost i)
      (inv_le_one_of_one_le₀ (one_le_pow₀ hz)))
  have hp := X.paths_pos
  have hu := inv_pos.mpr X.width_pos
  have hh := X.clip.radius_pos
  have ht := X.columns_ge
  have hs := X.price_pos
  have hn : y ≤ L := (Real.log_le_log_iff (by unfold y; linarith) (by unfold L; positivity)).mp hc
  unfold y at hn; change X.columns ≤ L ∧ X.supportExponent ≤ L
  constructor <;> linarith

private theorem blocks (h : Tabs C.path.levels) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ i in atTop, ((C.S.block i).val:ℝ) ≤ ε*C.S.scale (i+1) := by
  let Q := C.S
  let H := C.path.levels
  filter_upwards [h.cheap ε he] with i hi
  let f := Vac.fiat G (H.params (i+1)) (H.clock.hatBeta (i+1))
  have hf : 1 ≤ f := by
    unfold f Vac.fiat
    let A := H.params (i+1)
    let q := H.clock.hatBeta (i+1)
    have hn := A.paths_pos
    have hp := A.clip.quadratic_pos
    have hh : 0 ≤ Real.log q := (Real.log_pos (H.fits.delayed _)).le
    have ht : 0 ≤ (Fintype.card PlaqAxes:ℝ)*(A.clip.direct+A.paths^2) +
        4*Module.finrank ℝ G.Mat*(Real.log 16+Real.log q/2) := by positivity
    unfold A q at *; linarith
  let A : ℝ := (Q.block i).val
  let B : ℝ := A * ((H.clock.coverSize i:ℝ)^2)
  have h₁ : 1 ≤ A := by unfold A; exact_mod_cast (show 1 ≤ (Q.block i).val from (Q.block i).property)
  have h₂ : (1:ℝ) ≤ H.clock.coverSize i := by exact_mod_cast (show 1 ≤ H.clock.coverSize i from (H.budget i).B_pos)
  have hh : A ≤ B := le_mul_of_one_le_right (zero_le_one.trans h₁) (one_le_pow₀ h₂)
  change B^(4:ℕ)*f ≤ _ at hi
  have hx : B ≤ B^4 := by simpa using pow_le_pow_right₀ (h₁.trans hh) (show 1 ≤ 4 by decide)
  exact hh.trans (hx.trans ((le_mul_of_one_le_right (by exact pow_nonneg (zero_le_one.trans (h₁.trans hh)) _) hf).trans hi))

/-- `roof` follows already (on actual family/f, period stage too) by
this pre-L charge & Tabs. Only this additional slice of support estimate
has been verified available. -/
lemma roof_of_tabs (H : Tabs C.path.levels) : roof C f := by
  intro ε he
  obtain ⟨j,hj⟩ := eventually_atTop.mp (blocks H he)
  have hm : ∀ᶠ i in atTop, (C.path.levels.params i).supportExponent ≤ ε*C.S.scale i := by
    filter_upwards [eventually_gt_atTop j] with i hi
    cases i; omega
    exact le_trans (local_price C.path.levels _).2 (hj _ (by omega))
  filter_upwards [(cutoff_grows f).eventually hm] with i hi
  exact (Real.norm_of_nonneg (Real.exp_pos _).le).le.trans (Real.exp_monotone hi)







def hat_rate (C : Family G) (k : ℕ) (i : ℕ) := (C.path.levels.clock.hatBeta i ^ k)⁻¹

/-- Adapt Prices at ONE power k of coarse hat. No proof here that the
multi-source dynamics preserve the majorants at that choice. -/
def fees (C : Family G) (k : ℕ) (X : Prices) : Prices :=
    { X with coin := hat_rate C k
             legal i := inv_pos.mpr (pow_pos (zero_lt_one.trans (C.path.levels.fits.delayed i)) _) }


end YM.Push.RelayDifference
