import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Gauges
import YM.AnalyticBridge.RESET_INCOME_PORT.BulkFare
import YM.AnalyticBridge.RESET_INCOME_PORT.LogQuote
import YM.AnalyticBridge.RESET_INCOME_PORT.Sheen
import YM.AnalyticBridge.RESET_INCOME_PORT.Split
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sale
import YM.Extra.MULTISOURCE_BOUNDS.Step
import YM.Extra.MULTISOURCE_TRAJECTORIES.Blocks
import YM.Next.MAXWELL.Det
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Divided
import YM.Push.RELAY_DIFFERENCE.Birth
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix



set_option warningAsError false
set_option autoImplicit false

/-! Buy timing AFTER L and purchase the physical assumptions of Bought before Bar,
alongside even the selected covariance jet pricing schedule. Arbitrary further DelayLe on
the same stage data. Scalar *errors* only to the requested tolerance per output volume,
not bounding actual income at that tolerance. No claim of supplying Program or of fitting
these any more than the other engaged costs to an AFTER-the-fact history. -/
noncomputable section
namespace YM.SectorTools.ActualScalar
open Function Filter Set RG Wilson Lattice Input RG.Supply Pressure Bid Pressure.Testing Push.PriceCompiler
 Next.SectorChange Further GaussianScalar AnalyticBridge.ResetIncome AnalyticBridge Precision Tree Push.SectorMeasure
open scoped Topology Classical BigOperators ContDiff

variable {G : Gauge}



private lemma range_grows : Tendsto rangeSize atTop atTop := by
  refine tendsto_natCast_atTop_atTop.comp (f:=fun x : ℝ => radiusB x / 60) (tendsto_atTop.mpr fun m => ?_)
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (60*m)] with x hx
  omega

lemma stamp (G : Gauge) (d : Side) (p : Expense) {ε : ℝ} (hε : 0<ε) : ∀ᶠ x : ℝ in atTop,
    Timing p (rangeSize x) ∧ count d G * p.fog (rangeSize x) ≤ ε*Vac.Numbers.Hat x ^ ((11:ℝ)/5) := by
  let N := (count d G:ℝ); let C := 2*p.payment*p.high*p.payment + p.high*(p.payment*(p.high*p.payment))
  have hx := p.payment_pos; have he := p.high_pos; have hc : 0<C := by unfold C; positivity
  filter_upwards [range_grows.eventually p.delayed, Extra.Iteration.Scales.first (p.margin/120) 3 (by have := p.margin_pos; positivity),
    Work.E01.radiusB_tendsto.eventually_ge_atTop 120, eventually_gt_atTop (1:ℝ),eventually_ge_atTop (N*C/ε)] with x ht hl hz hi hv
  have hw : ((radiusB x:ℝ)/120) ≤ rangeSize x := (div_le_iff₀ (by norm_num : (0:ℝ)<120)).mpr (by
    exact_mod_cast (show radiusB x ≤ (radiusB x/60)*120 by omega))
  have ha : Real.exp (-p.margin * rangeSize x) ≤ x^(-(3:ℝ)) := (Real.exp_monotone (by
    linarith [mul_le_mul_of_nonneg_left hw p.margin_pos.le] : -p.margin * rangeSize x ≤ - (p.margin / 120) * radiusB x)).trans hl
  refine ⟨ht,?_⟩; rw [Vac.Numbers.Hat,Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith : 0≤x),← Real.rpow_mul (by linarith : 0≤x)]; norm_num
  have hf := p.fog_bound ht
  calc
    _ ≤ N * C * Real.exp (-p.margin * rangeSize x) := (mul_le_mul_of_nonneg_left hf (by unfold N; positivity : 0≤N)).trans_eq (by unfold Expense.correctionCost Expense.drift Expense.windowCost C; ring)
    _ ≤ ε * (x * x^(-(3:ℝ))) := (mul_le_mul_of_nonneg_left ha (by unfold N; positivity : 0≤N*C)).trans (by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (((div_le_iff₀ hε).mp hv).trans_eq (mul_comm ..)) (by positivity))
    _ ≤ _ := by
      have ht : x*x^(-(3:ℝ)) = x^(-(2:ℝ)) := by rw [show -(2:ℝ) = 1 + -3 by norm_num, Real.rpow_add (by linarith : 0<x),Real.rpow_one]
      rw [ht]; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hi.le (by norm_num)) hε.le

section cash
variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Z : ChartRatio G} {K : MapPrices}
open GaussianFieldAlignment

def Menu (D : Rolls c) (r : Tickets) (ε : ℕ → ℕ → ℝ) (j : ℕ) (x : ℝ) :=
    ∀ i, StepStages j i → let p := expense G (D.L j) (r j i)
    Timing p (rangeSize x) ∧ count (D.L j) G * p.fog (rangeSize x) ≤ ε j i*Vac.Numbers.Hat x ^ ((11:ℝ)/5)

structure Cash (W : Delays Θ) (Z : ChartRatio G) (K : MapPrices) (r : Tickets) (ε w a E : ℕ → ℕ → ℝ) : Prop where
  rings : Ringing K w W
  stars : Cosmos Z K W w a E
  table : Earned K W r
  clocked j x : W.betaEntry j ≤ x → Menu D r ε j x

/-- Before ANY Wait. Uniform even on further (same Rolls, same ε) scheduling increases. -/
theorem issue (W : Delays Θ) (hZ : LocalRatio Z) {w ε : ℕ → ℕ → ℝ} (hw : Ringing K w W) (he : ∀ j i, 0<ε j i)
    (k : ℕ → ℕ → ℕ) : ∃ (W' : Delays Θ) (r : Tickets) (a E : ℕ → ℕ → ℝ) (b : ℕ → ℕ → Covariance.Sale.Tab),
      DelayLe W W' ∧ OrderedDelays W' ∧ ∀ W'' : Delays Θ, DelayLe W' W'' → Cash W'' Z K r ε w a E ∧ Covariance.Sale.Enrolled W'' K k b := by
  obtain ⟨T,hT,b,hb⟩ := Covariance.Sale.next_table W K k
  have ht : DelayLe W T := ⟨hT.beta,hT.scale,hT.shells,hT.power⟩
  obtain ⟨Y,r,a,E,hY,_,H⟩ := issue_windows T hZ (Bid.recheck hT.beta hw)
  let B := Menu D r ε
  have h j : ∀ᶠ x : ℝ in atTop, B j x := by
    have h (i) := stamp G (D.L j) (expense G (D.L j) (r j i)) (he j i)
    filter_upwards [h j,h (j-1)] with x hx hy i hi
    obtain rfl | hh := eq_or_ne i j
    · exact hx
    have hz : i ≤ j ∧ j ≤ i+1 := hi
    have he : i=j-1 := by omega
    rw [he]; exact hy
  obtain ⟨U,hu,ho,hU⟩ := delay_extra Y B (fun _ _ _ => True) h (by simp)
  refine ⟨U,r,a,E,b,(ht.trans hY).trans hu,ho,fun V hv => ?_⟩
  obtain ⟨hR,hC,hE⟩ := H V (hu.trans hv)
  refine ⟨⟨hR,hC,hE,(hU V hv).1⟩,fun j i hi hj => ⟨(hb j i hi hj).1,fun P h h' y hy => ?_⟩⟩
  exact (hb j i hi hj).2 P h h' y (((hY.trans (hu.trans hv)).beta j).trans hy)
end cash
section step
open GaussianFieldAlignment
variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Input.Directed G I Z K P) {r : Tickets} {ε g a E : ℕ → ℕ → ℝ}

lemma costs_shift (m p : ℕ) : fiery G (B.a.clock.hatBeta m) ((B.a.clock.op m p).patch.L) = B.a.clock.threshold (m+1) := by
  have hl : B.a.clock.hatBeta (m+1)=betaF G (B.a.clock.hatBeta m) ((B.a.clock.op m p).patch.L) := by
    unfold Calendar.hatBeta betaF
    rw [Schedule.scale_succ]; change _ = _ + _ * Real.log (B.a.S.block m).val; unfold Levels.S; ring
  change temp _ = temp _; rw [hl]



end step
end YM.SectorTools.ActualScalar
