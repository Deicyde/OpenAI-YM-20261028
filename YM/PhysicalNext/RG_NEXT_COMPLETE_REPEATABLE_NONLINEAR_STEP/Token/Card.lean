import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Fluent
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Token
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare 
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S)
    (B : BudgetPoint) (β : ℝ) (k : S.Choices) {n : ℕ} {r C Z t a : ℝ}
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun x:Xs=> represent (tint G _ x))
local notation "M" => Pane.virgin T B β
variable {P : Teller G} (p : Intake P T t (Pane.virgin T B β))
def tramp (x : Xs) := S.push β (M).eval (V x)
def pures (x:Xs):= Real.log (tramp T B β x)
include p F
local notation "K" => prime G S.kernel n Z C β r
lemma lev (hp : PaintSupply G n Z) (h : (Fintype.card (Bond c):ℝ)≤ r) (x:Xs) (hx: ‖x‖<1) (hr : Brush n C 1 Real.exp 0) (ht : 0 ≤ K) : Brush n (K *tramp T B β x) 1 (tramp T B β) x:= by
  let U y i:=overall F T B β (V y) i
  have ha : S.patch.Branches S.kernel G:= p.ready.knobs.symm ▸ p.ready.kernel; have hC:= (M).envelope p.cap
  obtain ⟨d,hd⟩:=S.density_bound ha β; obtain ⟨v,hv⟩:=hC.cost
  have he y := amt F T B β _ P p (V y)
  have hy : ∀ᶠ y in 𝓝 x, ‖y‖<1 := continuous_norm.continuousAt.eventually (gt_mem_nhds hx)
  have hj : Meristem U x (F.order G) n := Meristem.points U (F.order G) ⟨fun _=> K*(|d| * |v|), integrable_const _, hy.mono fun y hh i=> by
    have hx:U y i ≤ |d| *|v|:= by
      unfold U; rw [Fare.total]; apply mul_le_mul ((hd _ _).trans (le_abs_self _)) ((le_abs_self _).trans ((hv _).trans (le_abs_self _))) _ (abs_nonneg _); rw [Pane.sparkling]; split <;> positivity
    exact (volumeQ F T B β i hp h y hh.le hr).climb (mul_le_mul_of_nonneg_left hx ht) le_rfl⟩ (Eventually.of_forall fun y=> (he y).1.meas) |>.1
  have hh : ∀ y, tramp T B β y=∫ i,U y i ∂F.order G:= fun y=> (he y).2
  simp_rw [funext hh]
  exact hj.buds _ (((he x).1.integrable _).const_mul _) zero_le_one (MeasureTheory.integral_const_mul ..).le (ae_of_all _ fun i=>volumeQ F T B β i hp h _ hx.le hr)

lemma thrush (hp : PaintSupply G n Z) (h : (Fintype.card (Bond c):ℝ)≤ r) (x:Xs) (hx: ‖x‖<1) (hr : Brush n C 1 Real.exp 0) (ht : 0 ≤ K) (hd : Brush n a 1 Real.log 1) (hh : 0 < tramp T B β x) : Brush n (clump n K a) 1 (fun y=> pures T B β y- pures T B β x) x:= by
  let s:= tramp T B β x; let f y:=s⁻¹*tramp T B β y
  have hp:= lev F T B β p hp h x hx hr ht; have hv : f x=1:= inv_mul_cancel₀ hh.ne'
  have hf := hp.smul s⁻¹; have hz := inv_pos.mpr hh; rw [Real.norm_of_nonneg hz.le, mul_left_comm, inv_mul_cancel₀ hh.ne',mul_one] at hf
  refine (composite hf (show Brush n a 1 Real.log (f x) from hv ▸ hd)).shimmy ?_
  filter_upwards [hp.smooth.continuousAt.eventually (lt_mem_nhds hh)] with y hy
  change _ = Real.log (f y); unfold f; rw [Real.log_mul hz.ne' hy.ne',Real.log_inv]; unfold pures; ring
end YM.PhysicalNext.Repeat.Token
