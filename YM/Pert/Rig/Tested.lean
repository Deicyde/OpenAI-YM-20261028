import YM.Pert.Rig.Moving
/-! Dominated convergence and exact normalizing volume of all placements (including the zero arity case). -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 350000
namespace YM.Pert.Rig
open Maxwell Lattice Extraction Set MeasureTheory Function Filter Full Topology Next.Rank.Radian Metric
variable (r : ℕ) (m : Motion) (K : ∀i,Grid (m.side i) r → ℂ) (f : Points r→ℂ)
variable {z : Points r}
def reporting (i:ℕ) := (m.t i:ℂ)^(4*r)*∑ j:Grid (m.side i) r, f (embedding (m.t i) j) * K i j
variable {m K f r} {ω : Set (Points r)} {G : Points r→ℂ}
lemma cap_radius (hc : HasCompactSupport f) : ∃ R : ℕ,∀ x,R < ‖x‖ → f x=0 := by
  obtain ⟨R,hR⟩ := (hc : IsCompact (tsupport f)).exists_bound_of_continuousOn (f:=id) continuousOn_id
  refine ⟨⌈R⌉₊, fun x hx => image_eq_zero_of_notMem_tsupport (fun ht=>not_lt_of_ge ((hR x ht).trans (Nat.le_ceil _)) hx)⟩
lemma integrable_chosen (R : ℕ) (hR : ∀x : Points r,R<‖x‖→f x=0) (i : ℕ) : Integrable (chosen m K f i) volume := by
  let u (v:field r) := f (tag (m.t i) v)*K i (place (m.side i) v)
  have he := (scans_integral (m.denom i) (R:=R) (m.t i) (m.positive i) u (fun x hx=>by dsimp [u]; rw [hR _ (lt_of_not_ge (fun hy=> hx (tent_valid _ (by rw [← m.exch i]; exact hy))))]; simp)).1
  unfold chosen F
  simpa only [chosen,F,u,comp_def,center_eq _ (m.positive i).ne'] using he
lemma piece_rule (R : ℕ) (hR : ∀x : Points r,R<‖x‖→f x=0) (i : ℕ) :
    scans (m.t i) (m.denom i) (fun u=> f (tag (m.t i) u)*K i (place _ u)) R = ∫ x, chosen m K f i x := (scans_integral _ _ (m.positive i) _ (fun x hx=>by rw [hR _ (lt_of_not_ge (fun hy=> hx (tent_valid _ (by rw [← m.exch i]; exact hy))))]; simp)).2.symm.trans (integral_congr_ae (Eventually.of_forall fun x => by dsimp only [comp_apply,chosen,F]; simp only [center_eq _ (m.positive i).ne']))
lemma grid_limit (hf : Continuous f) (hc : HasCompactSupport f) (hw : tsupport f ⊆ ω) (H : Arrives m K ω G) :
    Tendsto (reporting r m K f) atTop (𝓝 (∫ x : Points r, f x * G x)) := by
  obtain ⟨R,hR⟩ := cap_radius hc
  obtain ⟨C,hC,hbound⟩ := bounded_fee m K f hc hw H
  obtain ⟨L,hL⟩ := (isCompact_closedBall (0:Points r) (R : ℝ)).exists_bound_of_continuousOn hf.continuousOn
  let S:= closedBall (0:Points r) (R+4*r : ℝ)
  have hF (i:ℕ) (y) : ‖F m K f i y‖ = ‖f y‖*‖K i ((plot m (fun _=>y)) i)‖ := Complex.norm_mul ..
  have hf' (y) : ‖f y‖≤max L 0 := by
    by_cases h : y ∈ closedBall (0:Points r) (R:ℝ);· exact (hL y h).trans (le_max_left ..)
    rw [hR _ (lt_of_not_ge fun he=> h (mem_closedBall.mpr (by simpa))),norm_zero]
    exact le_max_right ..
  have hg : ∀ᶠ i in atTop, ∀ᵐ x:Points r, ‖chosen m K f i x‖ ≤ S.indicator (fun _=>max L 0 * C) x := by
    filter_upwards [hbound,m.shrinks.eventually (gt_mem_nhds (show (0:ℝ)<1 by positivity))] with i hi hv
    apply Eventually.of_forall; intro x
    let y := tag (m.t i) (address (m.t i) x)
    change ‖F m K f i y‖ ≤ _
    by_cases hy : y∈tsupport f ∧ ‖y‖≤ (R:ℝ)
    · rw [indicator_of_mem,hF]; exact mul_le_mul (hf' y) (hi y hy.1) (norm_nonneg _) (le_max_right ..)
      rw [mem_closedBall]; apply (dist_triangle_right x 0 (y)).trans ?_
      have he : dist x y ≤ 4*(r:ℝ) := by rw [dist_comm]; exact (approximate (m.positive _) x).trans (mul_le_of_le_one_right (by positivity) hv.le)
      rw [dist_comm 0,dist_zero_right]; linarith only [hy.2,he]
    have he : f y=0 := by
      simp at hy; by_cases hxy : y∈tsupport f; · exact hR y (hy hxy)
      exact image_eq_zero_of_notMem_tsupport hxy
    rw [hF,he,norm_zero,zero_mul]; apply Set.indicator_nonneg; intro _ _; exact mul_nonneg (le_max_right ..) hC
  have hb' : Integrable (S.indicator (fun _=>max L 0 * C)) := (integrable_indicator_iff measurableSet_closedBall).mpr (integrableOn_const measure_closedBall_lt_top.ne)
  let g := chosen m K f
  have hi' : ∀ᶠ i in atTop, AEStronglyMeasurable (g i) volume := Eventually.of_forall fun i=> (integrable_chosen R (m:=m) (K:=K) hR i).aestronglyMeasurable
  have hu := tendsto_integral_filter_of_dominated_convergence _ hi' hg hb' (Eventually.of_forall fun x : Points r=>chosen_limit m K f H hf hw x)
  apply hu.congr'; filter_upwards [available_rule m R] with i he; show (∫ x, chosen m K f i x)=_; exact ((piece_rule R hR i).symm.trans (scans_eq R he _ (m.exch i) f hR (K i)))
end YM.Pert.Rig
