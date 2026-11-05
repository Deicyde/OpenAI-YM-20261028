import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Eligibility
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Narrow
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Peak

/-!
# Packet factor and normalization deficits

Window Condensation PER link. Keep all tests once on a whole packet, incl
q even when suppressed. Erasures separate at boundaries. Require FLAGS at
support, Π & assignment of X supplied as-is. Use full empirical drows with
channel average. `spend` not the grant; proof combines *same* μ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

namespace Coat
variable (X : Coat T F)

def measure_g (Ñ : ChartRatio G) (β : ℝ) := Ñ.scale*(Real.sqrt (2*Real.pi)*gStep β)^Fintype.card G.ColorIndex

def existSeeds (A : Stores S) (O : ℕ) := A.place⊆ X.seeds.place ∧
    ∀ i∈A.dome (O*X.B), i∈A.flags ↔ i∈RG.flags (Pressure.temp X.x) X.V

def far_bills (A : Stores S) := Oriented.averaged fun s =>
    ∑ p∈posted (turnStore s A) (200*X.B), X.extracted X.μ s p

/-- Assign the free frozen positions of THIS F near A. -/
def pens (X : Coat T F) (A : Stores S) := (visit A (10*X.B)).filter (fun i => i∉F.trunks)

def steamLog (R : Rep G f) (Ñ : ChartRatio G) (a : ℝ) (A : Stores S) (u : Directions G f) :=
    -R.beta*(X.quoteNear A u+X.far_bills A) + (∑ i∈visit A (200*X.B), X.condensation i) +
      (∑ j∈X.plaza (A.dome (304*X.B)), X.gentry Ñ a u j) - (X.pens A).card*Real.log (measure_g Ñ R.beta)

def vias (S : StepData c f) (A : Stores S) (O : ℕ) := univ.filter fun i : Site f => Inside (S.ratio.parent i) A O

def steam (R : Rep G f) (Ñ : ChartRatio G) (l : Finset ℕ) (W a : ℝ) (A : Stores S) (u : Directions G f) :=
    let T' := 300*X.B
    let U:=X.input u
    Real.exp (X.steamLog R Ñ a A u)*Contract.order R l (vias S A T') U*(tickets A T' U X.k)*
      (profiles A X.χ T' X.x W U X.k X.V)*X.enforce a u (X.plaza (A.dome (304*X.B)))


lemma vapors (R : Rep G f) (Ñ : ChartRatio G) (l : Finset ℕ) (W a : ℝ) (A : Stores S) (u : Directions G f) :
    0 ≤ X.steam R Ñ l W a A u ∧ (X.steam R Ñ l W a A u≠0 → ∀ i∈X.plaza (A.dome (304*X.B)),X.cone a u i≠0) := by
  refine ⟨mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Contract.valid_pay ..).1)
    (ticket_nonneg ..)) (profiles_range ..).1) (X.conserve ..).1, fun h i hi he => ?_⟩
  exact False.elim (right_ne_zero_of_mul h (prod_eq_zero hi he))

lemma steam_le (R : Rep G f) (Ñ : ChartRatio G) (l : Finset ℕ) (W a : ℝ) (A : Stores S) (u : Directions G f) :
    |X.steam R Ñ l W a A u| ≤ Real.exp (X.steamLog R Ñ a A u+tollFee S.patch (300*X.B)*A.shares) := by
  let d:=300*X.B; let U := X.input u; let Y := tickets A d U X.k
  let c := Real.exp (X.steamLog R Ñ a A u)
  have he : c*Contract.order R l (vias S A d) U ≤ c := mul_le_of_le_one_right (Real.exp_pos _).le (Contract.valid_pay ..).2
  rw [Real.exp_add, abs_of_nonneg (X.vapors ..).1]; unfold steam; dsimp only
  have hh : 0 ≤ c*Contract.order R l (vias S A d) U * Y := mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (Contract.valid_pay ..).1) (ticket_nonneg ..)
  exact ((mul_le_of_le_one_right (mul_nonneg hh (profiles_range ..).1) (X.conserve ..).2).trans
    ((mul_le_of_le_one_right hh (profiles_range ..).2).trans (mul_le_mul he (tickets_le ..) (ticket_nonneg ..) (Real.exp_pos _).le)))

lemma aftermath {a C : ℝ} (u : Directions G f) (R : Rep G f) (h : Intake P T X.x R) (Ñ : ChartRatio G)
    (A : Stores S) (hA : 0≤C) {Q K : ℝ} (he : ∀ i, |X.gentry Ñ a u i|≤C) (hd : ∀ i, |X.condensation i| ≤ Q) (hQ : 0≤Q)
    (hp : -Real.log (measure_g Ñ R.beta) ≤ K) (hk : 0≤K) :
    X.steamLog R Ñ a A u ≤ -R.beta*X.quoteNear A u+
      (Q*swept S.patch.L ((200*X.B+1)+1) + C*swept S.patch.L ((304*X.B+1)+1)+K*swept S.patch.L ((10*X.B+1)+1))*A.shares := by
  have ha : 0 ≤ X.far_bills A := (by
    rw [← av_const 0]; exact av_mono fun s => Finset.sum_nonneg fun i _ => X.extracted_nn ..)
  have hx d (Y : Finset (Bond f)) (hh : Y⊆visit A d) (f : Bond f → ℝ) (b : ℝ) (he : 0≤b) (ht : ∀ i, f i≤b) :
      ∑ i∈Y, f i ≤ b*swept S.patch.L ((d+1)+1)*A.shares := by
    have hf := sum_le_sum (g:=fun _ => b) (s:=Y) (fun i _ => ht i)
    simp only [sum_const,nsmul_eq_mul] at hf; apply hf.trans
    unfold swept
    exact (mul_le_mul_of_nonneg_right (show (Y.card:ℝ) ≤ A.shares*(Animals.ballCost ((d+1)+1):ℝ)*
      (S.patch.L.val^4*Fintype.card Axis:ℕ) by exact_mod_cast (card_le_card hh).trans (touch_price S d A)) he).trans_eq (by ring)
  unfold steamLog
  have hX := hx (200*X.B) _ (Finset.Subset.refl _) X.condensation Q hQ fun i=> (le_abs_self _).trans (hd i)
  have hG : X.plaza (A.dome (304*X.B)) ⊆ visit A (304*X.B) := by
    intro i hi; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2.2⟩
  have hv := hx (304*X.B) _ hG (X.gentry Ñ a u) _ hA fun i=> (le_abs_self _).trans (he i)
  have hf := hx _ (X.pens A) (show X.pens A⊆visit A (10*X.B) from filter_subset ..) (fun _=> - Real.log (measure_g Ñ R.beta)) K hk fun _ => hp
  simp only [sum_const,nsmul_eq_mul] at hf
  nlinarith only [hX,hv,hf,mul_nonneg h.positive.le ha]

lemma scaled (Ñ : ChartRatio G) (he : LocalRatio Ñ) (L : Side) : ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ β : ℝ, 0<β → β ≤ 2*betaF G x L → -Real.log (measure_g Ñ β) ≤ C*Delay.bill G L x := by
  let A := Real.sqrt (2*Real.pi)
  let B := (Fintype.card G.ColorIndex:ℝ)
  let C := |Real.log Ñ.scale|+B*(|Real.log A|+|Real.log 2|)+B
  have hA : 0 < A := by unfold A; positivity
  have hf := he.scale
  have hb : 0 ≤ B := by unfold B; positivity
  have hC : 0 < 1+C := by unfold C; positivity
  refine ⟨_,hC,?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G L)).eventually_ge_atTop 1, Delay.shift_pos G L] with x hx hy β hβ hv
  have he : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hg : 0 < measure_g Ñ β := by unfold measure_g gStep; positivity
  unfold measure_g gStep; rw [Real.log_mul hf.ne' (by positivity),Real.log_pow,Real.log_mul hA.ne' (by positivity),Real.log_inv, Real.log_sqrt hβ.le]
  have hL := Real.log_le_log hβ hv
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hy.ne'] at hL
  have hp : (Real.log β)/2 ≤ |Real.log (2:ℝ)|+Delay.bill G L x := by
    have hz : 1 ≤ Real.log (betaF G x L) := hx
    unfold Delay.bill; nlinarith [le_abs_self (Real.log (2:ℝ)), abs_nonneg (Real.log (2:ℝ)),Nat.cast_nonneg (α:=ℝ) (radiusB x)]
  let W := Delay.bill G L x
  change -(Real.log Ñ.scale+B*(Real.log A+ -(Real.log β/2)))≤(1+C)*W
  unfold C; have hz : 1≤ W := Delay.bill_ge G L x
  nlinarith only [neg_le_abs (Real.log Ñ.scale),mul_le_mul_of_nonneg_left (neg_le_abs (Real.log A)) hb,
    mul_le_mul_of_nonneg_left hp hb, show B*(|Real.log A|+|Real.log 2|) ≤ B*(|Real.log A|+|Real.log 2|)*W from
       le_mul_of_one_le_right (by positivity) hz, le_mul_of_one_le_right (abs_nonneg (Real.log Ñ.scale)) hz,hz]
end Coat
end YM.ConnectedActivityE6
