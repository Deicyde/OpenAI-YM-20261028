import YM.Push.SECTOR_MEASURE.Profile
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Haar



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Broad patches: protect all ratios before dropping defaults

Extend *log* by a second copy of the profile so J
is then smoothly extended by one off patch, with positive real branch. The density itself is always multiplied by broad cuts, so zero there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric YM.Push.SectorMeasure
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {d : ℝ}

def broad (q : Chi) (d : ℝ) (x : G.Color) := q.innerShare d ‖x‖

lemma broad_smooth (q : Chi) (d : ℝ) : ContDiff ℝ ∞ (broad q d (G:=G)) := by
  have he : (fun x : G.Color => (‖x‖/d)^2) = (fun x => ‖x‖^2/d^2) := by funext x; rw [div_pow]
  unfold broad Chi.innerShare
  simp_rw [congr_fun he]
  exact q.smooth.comp ((contDiff_norm_sq ℝ).div_const _)

lemma broad_range (q : Chi) (x : G.Color) (d) : broad q d x ∈ Icc 0 1 := q.range _

lemma broad_span (q : Chi) (hd : 0 < d) (x : G.Color) (h : broad q d x ≠ 0) : ‖x‖ < 2*d := q.chosen_lt _ _ hd h

lemma broad_one (q : Chi) (hd : 0 < d) {x : G.Color} (h : ‖x‖ ≤ d) : broad q d x = 1 := by
  apply q.to_one
  have hh : ‖x‖/d ≤ 1 := (div_le_one hd).2 h
  have he : 0 ≤ ‖x‖/d := by positivity
  nlinarith

def logGuard (q : Chi) (Z : ChartRatio G) (d : ℝ) (x : G.Color) : ℝ := broad q (2*d) x * Real.log (Z.J x)

lemma logGuard_smooth (q : Chi) {Z : ChartRatio G} (h : LocalRatio Z) (hd : 0 < d) (hs : 4*d < Z.radius) :
    ContDiff ℝ ∞ (logGuard q Z d) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : ‖x‖ ≤ 4*d
  · have he : x∈ball 0 Z.radius := by simpa only [mem_ball,dist_zero_right] using hx.trans_lt hs
    have hf := ((h.germ x he).log (h.pos x he).ne').of_le (show (∞ : ℕ∞ω) ≤ ω by simp)
    exact (broad_smooth q (2*d)).contDiffAt.mul hf
  suffices hh : logGuard q Z d =ᶠ[𝓝 x] (fun _ => 0) by exact contDiffAt_const.congr_of_eventuallyEq hh
  have hl : 4*d < ‖x‖ := lt_of_not_ge hx
  filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hl)] with y hy
  change 4*d < ‖y‖ at hy
  have he : broad q (2*d) y = 0 := by
    by_contra hh
    have ht := broad_span q (d:=2*d) (by positivity) y hh
    linarith
  rw [logGuard,he,zero_mul]

def extended (q : Chi) (Z : ChartRatio G) (d : ℝ) (x : G.Color) : ℝ := Real.exp (logGuard q Z d x)

lemma extended_smooth (q : Chi) {Z : ChartRatio G} (h : LocalRatio Z) (hd : 0 < d) (hs : 4*d < Z.radius) :
    ContDiff ℝ ∞ (extended q Z d) := (logGuard_smooth q h hd hs).exp

lemma extended_pos (q : Chi) (Z : ChartRatio G) (d : ℝ) (x : G.Color) : 0 < extended q Z d x := Real.exp_pos _

lemma extended_agrees (q : Chi) {Z : ChartRatio G} (h : LocalRatio Z) (hd : 0 < d) (hs : 2*d < Z.radius)
    {x : G.Color} (hx : ‖x‖ ≤ 2*d) : extended q Z d x = Z.J x := by
  unfold extended logGuard
  rw [broad_one q (d:=2*d) (by positivity) hx,one_mul,Real.exp_log]
  exact h.pos _ (by simpa using hx.trans_lt hs)

lemma price_extended (q : Chi) {Z : ChartRatio G} {E : ℝ} (hd : 0 < d) (hp : ∀ x : G.Color, ‖x‖ ≤ 4*d →
    |Real.log (Z.J x)| ≤ E*‖x‖^2) (he : 0 ≤ E) (x : G.Color) :
    |Real.log (extended q Z d x)| ≤ E*(min ‖x‖ (4*d))^2 := by
  rw [extended,Real.log_exp,logGuard,abs_mul]
  obtain ⟨h,h'⟩ := broad_range q x (2*d)
  rw [abs_of_nonneg h]
  by_cases H : broad q (2*d) x = 0
  · rw [H,zero_mul]; positivity
  have hh := broad_span q (d:=2*d) (by positivity) _ H
  have hl : ‖x‖ ≤ 4*d := by linarith
  rw [min_eq_left hl]
  exact (mul_le_mul_of_nonneg_right h' (abs_nonneg _)).trans ((one_mul _).trans_le (hp _ hl))

section arrays
variable {ι : Type} [Fintype ι]

/-- All regular broad cutoffs; never on frozen group arguments. -/
def doors (q : Chi) (d : ℝ) (x : LogArray G ι) : ℝ := ∏ i, broad q d (x i)

def reserve (q : Chi) (Z : ChartRatio G) (d : ℝ) (x : LogArray G ι) : ℝ := ∏ i, extended q Z d (x i)

lemma doors_smooth (q : Chi) (d : ℝ) : ContDiff ℝ ∞ (doors q d (G:=G) (ι:=ι)) := by
  unfold doors; exact contDiff_prod fun i _ => (broad_smooth q d).comp (contDiff_apply _ _ i)

lemma reserve_smooth (q : Chi) {Z : ChartRatio G} (h : LocalRatio Z) (hd : 0 < d) (hs : 4*d < Z.radius) :
    ContDiff ℝ ∞ (reserve q Z d (ι:=ι)) := by
  unfold reserve; exact contDiff_prod fun i _ => (extended_smooth q h hd hs).comp (contDiff_apply _ _ i)

lemma reserve_pos (q : Chi) (Z : ChartRatio G) (d : ℝ) (x : LogArray G ι) : 0 < reserve q Z d x :=
  Finset.prod_pos fun _ _ => extended_pos ..





lemma every_door (q : Chi) {x : LogArray G ι} (h : doors q d x ≠ 0) (i : ι) : broad q d (x i) ≠ 0 := by
  intro hi; unfold doors at h; exact h (Finset.prod_eq_zero (Finset.mem_univ i) hi)

lemma protected_pay (q : Chi) {Z : ChartRatio G} (h : LocalRatio Z) (hd : 0 < d) (hs : 2*d < Z.radius)
    {x : LogArray G ι} (hx : doors q d x ≠ 0) : x ∈ mouth Z ∧ pay Z x = Z.scale ^ Fintype.card ι * reserve q Z d x := by
  have hi (i) := broad_span q hd _ (every_door q hx i)
  refine ⟨fun i _ => by simpa using (hi i).trans hs, ?_⟩
  simp only [pay,reserve,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  congr 1; exact Finset.prod_congr rfl fun i _ => (extended_agrees q h hd hs (hi i).le).symm

end arrays
end YM.Next.SectorChange
