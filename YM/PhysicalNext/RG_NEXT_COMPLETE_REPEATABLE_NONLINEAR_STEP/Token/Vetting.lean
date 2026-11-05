import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Trebles
/-! # Numeric costs normalize. Only log values in all neighborhoods used;
 approximate curvature real fuel not promised from E6 sector near Γ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Token
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare 
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {C C' Z u a s c' : ℝ} {j n : ℕ}
variable {f g : ℝ→ℝ} (r : ℝ→ℝ) (S : KernelChoices)
local notation "z" => (fun t=> betaF G t L)
lemma oatr (j:ℕ) (h : Rate G L 0 f) : Rate G L 1 (fun t=> oat j (f t) (2*z t)+oat j (f t) (2*z t)):= by
  have hr:= ((Rate.const 1).add h)
  have hr:= lumpRate j ((hr).add hr) h; have hv:= (((Rate.hat (G:=G) (L:=L)).mul_left 2).mul hr);rw [add_zero] at hv
  exact ((hv.add (hr.weaken (by linarith))).add (h.weaken (by linarith))).add ((hv.add (hr.weaken (by linarith))).add (h.weaken (by linarith))) -- constants 1 implicit?
lemma rising (j:ℕ) {u v : ℝ} (he: 0≤u) (ht: u≤v) (ha : 0 ≤ a) : clump j u a≤ clump j v a:= by unfold clump; gcongr
lemma rung (_h:0 ≤ C) (ha:0 ≤ a) (hb : C≤ s) : oat j a C ≤ oat j a s:= by unfold oat clump; dsimp only; gcongr
lemma primeN {t β v : ℝ} (h:0<β) (hv:β ≤ t) (hC: 0 ≤ C) (hp : 0≤ Z) (hm : 0 ≤ v) :
    0 ≤ prime G S n Z C β v ∧ prime G S n Z C β v ≤ prime G S n Z C t v := by
  have hu: 0 ≤ sizeN G S n v Z := by
    unfold sizeN priceCost Uniform.outerCost composeCost; have ht:= S.penalty_pos; have hx:=Uniform.shade_pos G; have hl:=G.colorScale_pos; positivity
  unfold prime; dsimp only; rw [abs_of_pos h,abs_of_pos (h.trans_le hv)]; refine ⟨?_, rising n (by positivity) (by gcongr) hC⟩; unfold clump; positivity
lemma climbF {p : ℝ} (h : Rate G L p f) (hp : 0 ≤ p) (k : ℕ) (v : ℝ) :
    Rate G L (p*(k:ℝ)) (fun t=>clump k (f t) v) := by
  unfold clump; simp only [mul_one]; apply Rate.mul_left; exact (((Rate.const 1|>.weaken hp).add ((Rate.const 1|>.weaken hp).add h)).pow k)
lemma primeR (h : Rate G L 0 r) : Rate G L (1*n) (fun t=> prime G S n Z a (2*z t) (r t)) := by
  unfold prime; dsimp only; apply climbF _ zero_le_one
  have hp := Brim.absolut (Rate.hat (G:=G) (L:=L)|>.mul_left 2)
  have hc:Rate G L 0 (fun t=> sizeN G S n (r t) Z):= (h.mul_left S.penalty).mul_right _
  simpa only [add_zero] using! (hp.mul hc).add (hp.mul hc)
lemma budgeting (κ : ℝ) (d : ℝ) (hd:0<d) (hg : κ<0) : ∀ᶠ t in atTop,
      Real.exp (-d*Delay.fineMonitor G L t^2)/a ≤ z t^κ ∧ Real.exp (-d*Delay.fineMonitor G L t^2)/a ≤ 1 := by
  have he : Rate G L (κ-1) (fun t=> Real.exp (-d * Delay.fineMonitor G L t^2) / a):= by
    have hh:= Rate.monitor_cutoff (G:=G) (L:=L) (a:=κ-1) hd (show 0<(2:ℝ) by norm_num); simp only [Real.rpow_two] at hh; simpa only [div_eq_mul_inv] using! hh.mul_right a⁻¹
  filter_upwards [he κ (by linarith), he.below (by linarith) 1 zero_lt_one] with t ht hk using ⟨(le_abs_self _).trans ht,(le_abs_self _).trans hk⟩
end YM.PhysicalNext.Repeat.Token
