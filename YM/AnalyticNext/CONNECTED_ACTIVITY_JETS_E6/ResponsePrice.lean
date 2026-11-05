import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Alert
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Crash
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Peak
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tax

/-!
# Probability budget of alarms

Gestures at one actual Air, amplitudes still billed separately (for tags,
gamma ratio etc.) Hits may share arbitrarily many Watch Horns.
Charge *distinct addresses* in one molecule, even though later clustering
may repeat several integrated molecules. Rooted envelope after all expenses
but before mark tree estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {L : Side}

namespace Coat
variable (X : Coat T F)

def catastrophe (ξ β : ℝ) (u : Finset (WarningAt c f)) := Poll.Crash (shouting S) (along (G:=G) S)
    (ξ*X.t*(gStep β)⁻¹) u (2*X.B)

def dice := Poll.sweep X.relating
instance : IsProbabilityMeasure X.dice := by unfold dice; infer_instance
lemma shocks (β ξ W a : ℝ) (R : Rep G f) (l : Finset ℕ) (z : Air f G)
    (hp : ∀ i,X.detect (X.liftA β z) W a R l i ≠0 → ¬ X.watch (shouting S i) ξ β (2*X.B) z)
    (u : Finset (WarningAt c f)) (he : ∀ i∈u,X.detect (X.liftA β z) W a R l i≠0) :
    z∈ X.catastrophe ξ β u := by
  intro i hi
  have hx := hp i (he i hi); unfold watch at hx; push Not at hx
  obtain ⟨p,hp,hv⟩ := hx; exact ⟨p,hp,hv.le⟩

/-- exposed costs incl hit inventories -/
def warning_count (L : Side) := L.val^4 * Fintype.card PlaqAxes +
    (Fintype.card Axis+(Fintype.card Axis+(1+L.val^4))) + Itinerary.density L
lemma staffed (S : StepData c f) : Census (warning_count S.patch.L) (shouting S) := by
  refine added (added (withType PlaqAxes (homeland S)) ?_) (perch S)
  refine added ?_ (added ?_ (added ordinary (homeland S)))
  all_goals exact withType Axis (ordinary (c:=c))

lemma charge_area (S : StepData c f) (x : ℝ) (T : Tube G S) (R : Rep G f) (h : Intake P T x R) :
    Delay.fineMonitor G S.patch.L x /2 ≤ Pressure.fiery G x S.patch.L*(gStep R.beta)⁻¹ := by
  have hx := h.height; let t := betaF G x S.patch.L
  have ht : 0≤t := le_trans zero_le_one hx.le
  have hp := h.window.1; let b := Real.sqrt t
  have he : b/2 ≤ Real.sqrt R.beta := by
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _); rw [Real.sq_sqrt h.positive.le, div_pow]
    rw [show b^2=t from Real.sq_sqrt ht]
    change t/2 ≤ _ at hp; linarith
  have hg := Delay.monitor_pos G S.patch.L x
  rw [gStep,inv_inv]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left he (temp_nonneg _))
  change _ ≤ b⁻¹ * Delay.fineMonitor G S.patch.L x * (b/2)
  have hb : 0<b := Real.sqrt_pos.mpr (zero_lt_one.trans hx)
  exact le_of_eq (by field_simp)

lemma alarm_bills (P : Teller G) (L : Side) {η r Q Y ξ : ℝ} (k : ℝ) (hξ : 0<ξ) :
    ∃ E, Rate G L k E ∧ ∀ᶠ x : ℝ in atTop,
    0≤ E x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
     (X : Coat T F), X.x=x → S.patch.L=L → Rotator P L η r Q Y X → ∀ R : Rep G f, Intake P T X.x R →
       ∀ v : Finset (WarningAt c f), X.dice.real (X.catastrophe ξ R.beta v) ≤ (E x)^v.card := by
  let p := Delay.fineMonitor G L
  let H (x : ℝ) := p x ^ ((1:ℝ)/2)
  let B x := radiusB x; let ε := ξ/4
  let u := Census.tubularPrice G L; let W := warning_count L
  let M := payE η r Q u; let V (x : ℝ) := Animals.ballCost (2*B x)
  let E (x : ℝ) := (V x:ℝ)* (u:ℝ)*2*Real.exp (-H x*ε)
  have hp : Rate G L k (fun x=>Real.exp (-H x*ε)) := by
    refine (Rate.monitor_cutoff (show 0< ε by unfold ε; positivity) (show (0:ℝ) < 1/2 by norm_num)).congr
      (Eventually.of_forall (fun x => ?_))
    exact congr_arg Real.exp (show -H x*ε=-ε*H x by ring)
  have he := Census.width_rate G L 2 0; simp only [add_zero] at he
  refine ⟨E,(by convert (((he.mul_right u).mul_right 2).mul hp) using 1
                linarith),?_⟩
  obtain ⟨A,hA,h⟩ := width_bound G L 2 0
  simp only [add_zero] at h
  have hε : 0<ε := by unfold ε; positivity
  filter_upwards [Delay.monitor_pays G L 4 (show 0≤ A*(W:ℝ) by positivity) (show (0:ℝ)<1/2 by norm_num),
    Delay.monitor_pays G L 0 (show 0≤ |M|/ε by positivity) zero_lt_one] with x hx hy
  have hf : V x ≤ A*Delay.bill G L x^4 := h _
  have hv : 0 < H x := by unfold H; exact Real.rpow_pos_of_pos (Delay.monitor_pos ..) _
  refine ⟨(by unfold E; positivity),?_⟩; intro c f S T F X hg hL hR R hr v
  subst x
  let x := X.x
  have ht : H X.x*H X.x=p X.x := by unfold H; rw [← Real.rpow_add (Delay.monitor_pos ..)]; norm_num; rfl
  unfold dice catastrophe
  unfold E; rw [show -H X.x*ε=-(ε*H X.x) by ring]
  refine Poll.shattered _ _ _ hR.fullC.posSemidef (fun v => (le_abs_self _).trans
    (Control.top (hR.scale.mate X.shutter) hR.full.prices.le v)) (by unfold u; rw [← hL]; exact entering S) (p:=u) (m:=W)
      (by unfold W; rw [← hL]; exact staffed S) v (2*X.B) (by positivity) ?_
  have hm : M/2 ≤ ε*p X.x := by
    rw [pow_zero,mul_one,Real.rpow_one] at hy
    have he := (div_le_iff₀ hε).mp hy
    have hv : 0 ≤ p X.x := (Delay.monitor_pos ..).le
    nlinarith [mul_nonneg hε.le hv, le_abs_self M]
  have hz : ε*H X.x *((V X.x:ℝ)*W) ≤ ε*p X.x := by
    have hp : (V X.x:ℝ)*W ≤ H X.x := (mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg W)).trans
      ((le_of_eq (by ring : A*Delay.bill G L X.x^4 * (W:ℝ) = A*(W:ℝ)*Delay.bill G L X.x^4)).trans hx)
    rw [← ht]; refine (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ ε*H X.x)).trans_eq (by ring)
  apply (add_le_add hm hz).trans
  have hp := charge_area S X.x T R hr
  change Delay.fineMonitor G S.patch.L X.x /2 ≤ X.t*(gStep R.beta)⁻¹ at hp
  rw [hL] at hp
  unfold ε p; nlinarith only [mul_le_mul_of_nonneg_left hp hξ.le]
end Coat
end YM.ConnectedActivityE6
