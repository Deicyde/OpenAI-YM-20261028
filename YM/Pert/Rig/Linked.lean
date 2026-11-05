import YM.Pert.Rig.Tested
import YM.Pert.Warp.Horizons
/-! Regulator-removal theorem for order zero of the tested Wilson prescription. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option maxRecDepth 3500
noncomputable section
namespace YM.Pert.Rig
open Filter Lattice Full Maxwell Align Extraction Function Labels Topology Set MeasureTheory Classical

def denom (L : Side) (m : ℕ) : Side := ⟨L.val^m, by positivity⟩
theorem exchangePt (L : Side) (m : ℕ) : Full.topSpacing L m = ((denom L m).val:ℝ)⁻¹ := by rw [Full.topSpacing,zpow_neg, zpow_natCast]; change _ = (((L.val^m:ℕ):ℝ))⁻¹; rw [Nat.cast_pow]
def routine (L : Side) (h : 1 < L.val) : Motion where
  side := Full.period L
  denom := Rig.denom L
  t := Full.topSpacing L
  positive m := Full.spacing_pos L m
  exch m := exchangePt L m
  shrinks := cutoff_rule L h
  available := by simpa only [mul_comm, pow_one] using size_rule L h 1

def path (T : Itinerary) (σ : ℕ→ℕ) (h : Tendsto σ atTop atTop) : Itinerary where
  period := T.period ∘σ
  grid := T.grid ∘ σ
  gap := T.gap ∘ σ
  grid_eq m := T.grid_eq _
  clears := T.clears.comp h
  positive m := T.positive _
  cutoff := T.cutoff.comp h
  huge e := (T.huge e).comp h
  even_at m := T.even_at _
variable {G : Gauge} (d : ℕ) {r : ℕ} (A : Frames G) (L : Side) (hL : 1<L.val)
local notation "atZero" => PowerSeries.constantCoeff (R:=ℂ)
include hL
variable (p : Fin r→(freeTable A).Field d) (T : Motion)
-- temporary use routine below

private lemma frontier : Arrives (routine L hL) (fun i o=>atZero (Full.row d A (topSpacing L i) o p)) (conf r)
    (fun z=> Wick.moment G z (fun j=> reduceEq (sections d A (p j)))) := by
  intro σ ha z hz o ho
  let R := path (itinerary L hL) σ ha
  have hs (j : Fin r) : Home R (fun i=>o i j) (z j) := by
    have hj := (PiLp.continuous_apply 2 (fun _ : Fin r=>E4) j).continuousAt.tendsto.comp ho
    exact hj
  exact Warp.row_limit d R o z hz hs (fun i => four_places hL (σ i)) _ p
private theorem reporting_zero (f : Points r→ℂ) (m : ℕ) :
    reporting r (routine L hL) (fun i o=>atZero (Full.row d A (topSpacing L i) o p)) f m = atZero (profile d r A L m f p) := by
  simp only [profile, routine, reporting, MultilinearMap.sum_apply, _root_.map_sum, MultilinearMap.smul_apply, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.constantCoeff_C, Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr (Finset.ext (fun i => by simp))
  intro i _; rfl
private lemma reads (p : (freeTable A).Field d) :
    Extra.FD.writes A d p = reduceEq ((sections d A) p) := by
  conv_lhs => rw [← RawLabels.physical_round A p]
  rw [show RawLabels.enroll A d (RawLabels.physicalLabel A d p) = (freeTable A).project d ((A.level d).coords (RawLabels.physicalLabel A d p)) from
    (rfl : _ = _), Extra.FD.writes_project] -- need specify
  change reduceEq ((A.level d).coords.symm ((A.level d).coords _)).val = _; rw [LinearEquiv.symm_apply_apply]; rfl

theorem zerothProfile (f : Points r→ℂ) (h₀ : Continuous f) (h₁ : HasCompactSupport f) (hf : tsupport f ⊆ conf r) :
    Tendsto (fun m=>PowerSeries.coeff 0 (profile d r A L m f p)) atTop
      (𝓝 (∫ x : Points r, f x * Ward.disc (fun j=> (Sigma.mk d (p j) : (freeTable A).Tag)) x)) := by
  have he := grid_limit h₀ h₁ hf (frontier d A L hL p)
  have hm := reporting_zero d A L hL p f
  unfold Ward.disc
  simp_rw [Extra.FD.writes_eval]
  change Tendsto _ _ (𝓝 (∫ x : Points r, f x * Wick.moment G x (fun j : Fin r=>Extra.FD.writes A d (p j))))

  simp only [reads d A L hL]
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using he.congr hm
end YM.Pert.Rig
