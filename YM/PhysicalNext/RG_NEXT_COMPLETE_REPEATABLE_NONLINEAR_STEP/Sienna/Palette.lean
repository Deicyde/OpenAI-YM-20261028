import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Quarry
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Nuts
/-! # Lap caps numeric vol. only on auxiliary Vol. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sienna
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} (L : Side) {f w : ℝ→ℝ} {p C η σ l : ℝ} {n : ℕ} {Q : KernelChoices}
local notation "Z" => (fun t=> betaF G t L)
local notation "M" => (fun t=> Delay.fineMonitor G L t)
local notation "F" => (fun t=> Pressure.fiery G t L)
local notation "U" => eaves G L
local notation "δ" => furl G L
local notation "D" => wick G L
lemma posts (P : Patch) (O : ChartRatio G) (b : Clip) (A : Before G σ C P.J Q (n+3)) (E : FiberFee O ((n+3)+1))
    (h : Bolt G L f) : let p t:= pam n O b P A (f t) (f t) E (loopBill G L t)
      Rate G L 0 p ∧ ∃ a v : ℝ→ℝ, Bolt G L a ∧ Bolt G L v ∧ ∀ t,p t=a t+v t*M t := by
  intro p; let T:= A.tables b P
  let q t (v:ℝ):= pam n O b P A (f t) (f t) E v
  let s (z:ℝ) t:= q t z
  let v t:= s 2 t - s 0 t
  have ht z : Bolt G L (s z):= by
    have hl (k:ℕ) (C:ℝ) : Bolt G L (fun t=> tollS (f t) k C) := (h.nod k).times (Bolt.still _)
    let J t:= lensT n T (f t); have hJ:Bolt G L J := (Bolt.still _).joins (hl _ _)
    have hy:Bolt G L (fun t=> mineshaft n T (f t)):= (hl _ _).times (Bolt.still _)
    have hk:Bolt G L (fun t=> thickness T n (f t)):= (hl _ _).times (Bolt.still _)
    have hx:Bolt G L (fun t=> atomW G (n+4) A.Z σ z (f t) (f t)) := h.times (hl _ _)
    exact (((h.times hJ).joins hy).joins (hx.joins (h.times (Bolt.still (taxR (n+4) E.cost G))))).joins hk
  have hv:Bolt G L v:= by
    let e := s 0; have hh := (ht 2).joins ((Bolt.still (-1)).times (ht 0)); unfold v; simp only [neg_mul,one_mul,← sub_eq_add_neg] at hh; exact hh
  have he t:p t=s 0 t+v t*M t:= by unfold p v s q pam atomW tollS ConnectedActivityE6.loopBill; dsimp only; ring
  refine ⟨?_,s 0,v,ht 0,hv,he⟩; simp_rw [funext he]; apply Rate.add (ht 0|>.uses); exact (by simpa only [zero_add] using hv.uses.mul (Rate.monitor (G:=G) (L:=L)))
lemma minted (C' : ℝ) (h:Bolt G L f) : ∀ᶠ t in atTop,
    ∀ β:ℝ, 0≤β→β≤2*Z t → ∀ b:BudgetPoint, b.threshold=F t → 1≤ f t → f t* PathData.loopsPrice b β C' (loopBill G L t) ≤ 1:= by
  let k t:=2*Z t
  have hk : Rate G L (-1/2) (fun t=> k t*(|C'| *F t^3 + |C'| *F t^4)):= by
    have hr := Rate.flame (G:=G) (L:=L); have hb:= Rate.hat (G:=G) (L:=L)|>.mul_left 2
    exact (hb.mul (((hr.pow 3).mul_left _).add ((hr.pow 4|>.mul_left _).weaken (by norm_num)))).weaken (by norm_num)
  have hζ := hk.add (((loopBill_rate G L).mul (Rate.flame (G:=G) (L:=L)|>.pow 2)).weaken (by norm_num))
  filter_upwards [(h.uses.mul hζ).below (by norm_num) _ zero_lt_one, Delay.shift_pos G L] with t ht hy β hb hx b H hr
  unfold PathData.loopsPrice; rw [H]; apply le_trans _ ((le_abs_self _).trans ht); apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hr); refine add_le_add ?_ le_rfl; have hz : 0 ≤ F t:= temp_nonneg _
  apply le_trans (mul_le_mul_of_nonneg_left (le_trans _ le_rfl) hb) (mul_le_mul_of_nonneg_right hx (show 0 ≤ |C'| * fiery G t L^3+ |C'| *fiery G t L^4 by positivity)); gcongr <;> exact le_abs_self _

lemma crayon (G : Gauge) (d C : ℝ) (h : Bolt G L f) : ∀ᶠ t in atTop,
    ∀ β:ℝ, 0 ≤β → β ≤ 2*betaF G t L → ∀ A:BudgetPoint, A.threshold ≤ 2*Pressure.fiery G t L → 1≤f t →
      ∀ x:ℝ, 0≤x → x≤eaves G L t → β * (f t*d*x^5 + f t*(C*A.threshold^3+C*A.threshold^4)) ≤ 1:= by
  let a t:= eaves G L t; let b t:= 2*Pressure.fiery G t L; let w t:= f t*(|C| *b t^3+|C| *b t^4); let p t:=f t*|d| *a t^5
  have he:= (Rate.flame (G:=G) (L:=L)).mul_left 2
  have hp : Rate G L (-(1/4)) fun x=> (2*betaF G x L)*(p x+w x) := by
    have hr : Rate G L (-(3/2)) p:= ((h.uses.mul_right |d|).mul (edge G L|>.pow 5)).weaken (by norm_num [vow]); have hn : Rate G L (-(3/2)) w := (h.uses.mul (((he.pow 3).mul_left _).add ((he.pow 4|>.mul_left _).weaken (by norm_num)))).weaken (by norm_num)
    exact ((Rate.hat (G:=G) (L:=L)|>.mul_left 2).mul (hr.add hn)).weaken (by norm_num)
  filter_upwards [hp.below (by norm_num) _ zero_lt_one, Delay.shift_pos G L] with t ht he β hβ hx A hA hQ x hxx hy
  have ha:0≤a t:= Real.rpow_nonneg (by change 0≤ betaF G t L; positivity) _
  have hv : 0 ≤ f t:= zero_le_one.trans hQ; have h:=A.threshold_pos; have hT: 0 ≤ b t:=h.le.trans hA
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hβ) ((mul_le_mul_of_nonneg_right hx (by unfold p w; positivity)).trans ((le_abs_self _).trans ht))
  unfold p w; change A.threshold≤b t at hA; change x≤a t at hy; gcongr <;> exact le_abs_self _
end YM.PhysicalNext.Repeat.Sienna
