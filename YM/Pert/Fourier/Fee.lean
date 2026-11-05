import YM.Pert.Fourier.Cellular
/-! Quadrature cost on the common unweighted direct self line (fixed cover displacement). Keep power rate before engineering scaling. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Cellular
open Topology Lattice Filter MeasureTheory Set Metric Function
open scoped BigOperators Classical ContDiff

@[simp] lemma do_zero : dtype 0 = 0 := by simp [dtype,Full.delta]
lemma currency {x : E4} (hx : x∈cells) : ‖x‖^2 ≤ dtype x /4 := by
  have e := Full.delta_bound (cells_cube x |>.mp hx)
  have hp := Real.pi_pos
  rw [norm_smul,norm_mul,Real.norm_of_nonneg (show (0:ℝ)≤2 by norm_num),Real.norm_of_nonneg (by positivity : 0≤Real.pi),←dtype] at e
  suffices h : 4*‖x‖^2≤dtype x/4 by nlinarith only [h,sq_nonneg ‖x‖]
  exact le_of_mul_le_mul_left (a:=Real.pi^2) (by linarith only [e]) (sq_pos_of_pos hp)
lemma inv_currency {x : E4} (hx : x ∈ cells) : |(dtype x)⁻¹| ≤ (‖x‖^2)⁻¹ := by
  by_cases he : x=0; · simp [he]
  have hp := norm_pos_iff.mpr he
  have h : ‖x‖^2 ≤ dtype x := by nlinarith only [sq_nonneg ‖x‖,currency hx]
  have hv : 0≤(dtype x)⁻¹ := inv_nonneg.2 <| le_trans (sq_nonneg _) h
  rw [abs_of_nonneg hv]; gcongr
lemma handful (f : E4→ℝ) (h : ContDiff ℝ ∞ f) : ∃ c≥0,∀ x ∈ cells, ∀ y∈ cells, ‖f x - f y‖ ≤ c*‖x-y‖ := by
  obtain ⟨C,H⟩ := isCompact_closedBall (0:E4) 1 |>.exists_bound_of_continuousOn (h.continuous_fderiv (by simp)).continuousOn
  exact ⟨max C 0,le_max_right ..,fun x hx y hy => (Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (fun _ _=>h.differentiable (by simp) _) H (convex_closedBall (0:E4) 1) (cells_ball hy) (cells_ball hx)).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))⟩
lemma dtype_diff : ContDiff ℝ ∞ dtype := by unfold dtype Full.delta; apply ContDiff.sum; intro k _; fun_prop
lemma stash_diff (a : Cover) : ContDiff ℝ ∞ (clock a) := by unfold clock Full.corner; apply ContDiff.cos; apply ContDiff.sum; intro k _; fun_prop
lemma clock_price (a : Cover) (u : E4) : |clock a u| ≤ 1 := Real.abs_cos_le_one _
lemma inv_rate (a : Cover) {x : E4} (hx:x∈cells) : ‖trace a x‖ ≤ (‖x‖^2)⁻¹ := by
  unfold trace; simp only [norm_mul, Real.norm_eq_abs]; grw [clock_price a x, mul_one]; exact inv_currency hx
lemma inv_visits (a : Cover) (n : Side) (x : E4) (hx : x∈cells) (hy : visit n x∈cells) : ‖trace a (visit n x) - trace a x‖ ≤ 26*(‖x‖^2)⁻¹ := by
  let y:=visit n x; have he := inv_rate a hy
  suffices h : ‖trace a y‖ ≤ 25*(‖x‖^2)⁻¹ by nlinarith only [norm_sub_le (trace a y) (trace a x), inv_rate a hx,h]
  by_cases H : y=0; · rw [H]; unfold trace; rw [do_zero,inv_zero,zero_mul, norm_zero]; positivity
  by_cases h:x=0; · exact False.elim (H (by ext i; rw [show y=(0:E4) by ext j; unfold y visit; change _ = (0:ℝ); rw [Band.reads_wrap, h]; change (↑⌈(0:ℝ)/(n.val:ℝ)⁻¹⌉:ℝ)/_ = _; simp])) -- check simp. actually visit n zero.
  have hv : ‖x‖ ≤ 5*‖y‖ := by have hw := norm_sub_le x y; nlinarith only [show ‖x‖≤‖y-x‖+‖y‖ by simpa only [sub_sub_cancel, norm_sub_rev,add_comm] using norm_sub_le y (y-x),visit_floor _ _ H, visit_eps n x]
  have hw := norm_pos_iff.mpr H; have hv' := norm_pos_iff.mpr h
  apply le_trans he

  rw [←one_div, ←div_eq_mul_inv, div_le_div_iff₀ (sq_pos_of_pos hw) (sq_pos_of_pos hv')]; nlinarith only [hv,hw,hv']
lemma inv_matrix (a : Cover) : ∃ c≥0,∀ {r : ℝ},0 < r → r≤1 → ∀ x∈cells,∀ y∈cells,r ≤ ‖x‖ → r ≤ ‖y‖ → ‖trace a y - trace a x‖ ≤ (c/r^4)*‖y-x‖ := by
  obtain ⟨A,hA,ha⟩ := handful dtype dtype_diff
  obtain ⟨B,hB,hb⟩ := handful _ (stash_diff a)
  refine ⟨B+A,add_nonneg hB hA,?_⟩
  intro r hr h1 x hx y hy hx0 hy0
  have hv (x : E4) (hx : x∈cells) (ht : r≤‖x‖) : |(dtype x)⁻¹| ≤ (r^2)⁻¹ := (inv_currency hx).trans (by gcongr)
  have he (x:E4) (hx : x∈cells) (ht : r ≤ ‖x‖) : dtype x ≠ 0 := fun H=> by have := currency hx; rw [H] at this; nlinarith only [this,ht,hr]
  rw [show trace a y - trace a x = (clock a y - clock a x)*(dtype y)⁻¹ + ((dtype x - dtype y)*(dtype y)⁻¹)* ((dtype x)⁻¹*clock a x) from by unfold trace; field_simp [he y hy hy0,he x hx hx0]; ring]
  apply (norm_add_le ..).trans
  simp only [norm_mul]
  apply (add_le_add (mul_le_mul (hb _ hy _ hx) (hv y hy hy0) (abs_nonneg _) (by positivity)) (mul_le_mul (mul_le_mul (ha _ hx _ hy) (hv y hy hy0) (abs_nonneg _) (by positivity)) (mul_le_mul (hv _ hx hx0) (clock_price _ _) (abs_nonneg _) (by positivity)) (by positivity) (by positivity))).trans
  have h2 : r^2≤1 := pow_le_one₀ hr.le h1
  push_cast; rw [norm_sub_rev y]; field_simp; nlinarith only [show B*‖x-y‖*r^2 ≤ B*‖x-y‖*1 from mul_le_mul_of_nonneg_left h2 (mul_nonneg hB (norm_nonneg _))]

def spike (r : ℝ) := (ball (0:E4) (2*r)).indicator fun q=> (‖q‖^2)⁻¹
lemma spike_int (r : ℝ) : Integrable (spike r) := (integrable_indicator_iff measurableSet_ball).2 (integrableOn_ball_of_norm_le_rpow (by simp : 1≤Module.finrank ℝ E4) (α:=2) (by norm_num [E4]) (C:=1) (Eventually.of_forall fun q:E4=> by rw [Real.rpow_neg (norm_nonneg q),show (2:ℝ)=((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast, Real.norm_of_nonneg (by positivity)]; exact (one_mul _).symm.le) (by fun_prop))
lemma strike (a : Cover) (n : Side) : Integrable (cells.indicator (trace a)) := by
  refine (spike_int 3).mono' (Measurable.aestronglyMeasurable (by unfold trace; apply Measurable.indicator _ cells_closed.measurableSet; exact (dtype_diff.continuous.measurable.inv.mul ((stash_diff _).continuous.measurable)))) <| Eventually.of_forall ?_
  intro x
  unfold spike
  by_cases hx:x∈cells
  · rw [indicator_of_mem hx, indicator_of_mem (mem_ball.mpr (by rw [dist_zero_right]; linarith [cells_bd hx]))]; exact inv_rate _ hx
  rw [indicator_of_notMem hx]; exact (le_of_eq norm_zero).trans (indicator_nonneg (fun x (_hx:x∈ball (0:E4) (2*3))=> by positivity) _)
lemma spike_pos {r : ℝ} (hr : r>0) : (∫ k, spike r k) = r^2 * ∫ k, spike 1 k := by
  have h : ∀ x, r^2 * spike r (r•x) = spike 1 x := by
    intro x
    have h1' : (r•x)∈ball (0:E4) (2*r) ↔ x∈ball 0 (2*1) := by simp only [mem_ball,dist_zero_right,mul_one,norm_smul,Real.norm_of_nonneg hr.le]; rw [mul_comm (2:ℝ) r]; exact mul_lt_mul_iff_right₀ hr
    unfold spike; by_cases hx : x∈ball (0:E4) (2*1)
    · rw [indicator_of_mem hx,indicator_of_mem (h1'.mpr hx),norm_smul,Real.norm_of_nonneg hr.le,mul_pow,mul_inv]
      field_simp
    rw [indicator_of_notMem hx,indicator_of_notMem (mt h1'.mp hx),mul_zero]
  have hh := integral_const_mul (μ:=volume) (r^2) (fun x=>spike r (r • x)); simp_rw [h] at hh
  have hd (f : E4→ℝ) := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume f _ (hR:=hr.le)
  simp only [YM.Next.Rank.Radian.spaceD,smul_eq_mul] at hd
  rw [hd (spike r)] at hh
  field_simp at hh; nlinarith only [hh]

lemma linear_der (a : Cover) : ∃ C≥0,∀ {r : ℝ},0<r → r≤1 → ∀ {n : Side}, 8*(n.val:ℝ)⁻¹ ≤ r →∀ {x:E4}, x∈cells → visit n x∈cells → r<‖x‖ → ‖trace a (visit n x) - trace a x‖ ≤ C*((n.val:ℝ)⁻¹)/r^4 := by
  obtain ⟨A,hA,H⟩ := inv_matrix a
  refine ⟨A*(2^4)*4,by positivity,?_⟩; intro r hr h1 n hn x hx hy hw
  let y:= visit n x
  have hey : r/2 ≤ ‖y‖ := by have he := norm_sub_le y (y-x); rw [sub_sub_cancel] at he; linarith only [hw,hn, he,visit_eps n x]
  apply le_trans (le_trans (H (half_pos hr) (by linarith) x hx y hy (by linarith) hey) (mul_le_mul_of_nonneg_left (visit_eps n x) (by positivity)))
  apply le_of_eq; field_simp
lemma toroid_cost (a : Cover) : ∃ C≥0,∃ A≥0,∀ {n : Side}, Even n.val → ∀ {r : ℝ}, 0< r → r≤1 → 8*(n.val:ℝ)⁻¹ ≤ r →
   ‖(∫ k,cells.indicator (fun p=> trace a (visit n p)) k)- (∫ k, cells.indicator (trace a) k)‖ ≤ C*(r^2) + A*(n.val:ℝ)⁻¹ / r^4 := by
  obtain ⟨A,hA,H⟩ := linear_der a
  let v:=A*volume.real cells
  have hp : ∀ x,0 ≤ spike 1 x := indicator_nonneg (fun x _=>by exact inv_nonneg.2 (sq_nonneg _))
  refine ⟨26*∫ k,spike 1 k, by apply mul_nonneg (by positivity) <| integral_nonneg hp,v,(mul_nonneg hA ENNReal.toReal_nonneg),?_⟩
  intro n he r hr h1 hn
  let C:= (n.val:ℝ)⁻¹ /r^4
  have hC : 0≤A*C := mul_nonneg hA (show 0≤ C by dsimp [C]; positivity)
  let Base:=cells.indicator (fun _=> A*C)
  rw [← MeasureTheory.integral_sub (integrate_visit n he (trace a)).1]
  rotate_left
  · exact strike a n
  refine (norm_integral_le_of_norm_le (g:=fun x=>26*spike r x + Base x) ?_ ?_).trans (le_of_eq ?_)
  · exact (MeasureTheory.Integrable.add ((spike_int r).const_mul 26) ((integrable_indicator_iff cells_closed.measurableSet).2 (integrableOn_const cells_compact.measure_ne_top)))
  · filter_upwards [cell_AE] with x hx
    by_cases ht : x∈cells
    · rw [indicator_of_mem ht,indicator_of_mem ht, show Base x = A*C from indicator_of_mem ht _]
      have hv : visit n x∈cells := by
        apply (cells_cube (visit n x)).mpr; unfold visit; obtain ⟨p,hh⟩ := (marked_cell n he hx).mp ht;rw [←hh,visit_defensive]; apply Full.moment_cube
      by_cases h : ‖x‖ ≤ r
      · have hb : x∈ball (0:E4) (2*r) := by rw [mem_ball,dist_zero_right]; linarith only [h,hr]
        unfold spike; rw [indicator_of_mem hb]
        exact (inv_visits a n x ht hv).trans (le_add_of_nonneg_right hC)
      grw [H hr h1 hn ht hv (lt_of_not_ge h),show (A*((n.val:ℝ)⁻¹) / r^4)=A*C from by dsimp only [C];ring]; unfold spike; have hx0 := indicator_nonneg (s:=ball (0:E4) (2*r)) (f:=fun x:E4=>(‖x‖^2)⁻¹) (fun q _ => by positivity) x; exact le_add_of_nonneg_left (by positivity)
    rw [indicator_of_notMem ht,indicator_of_notMem ht,sub_self]; exact (le_of_eq norm_zero).trans (add_nonneg (mul_nonneg (by positivity) (indicator_nonneg (fun q (_hx:q∈ball (0:E4) (2*r))=>inv_nonneg.2 (sq_nonneg _)) x)) (indicator_nonneg (fun _ _=> hC) x))
  rw [integral_add ((spike_int r).const_mul _)]; swap
  · exact (integrable_indicator_iff cells_closed.measurableSet).2 (integrableOn_const cells_compact.measure_ne_top)
  unfold Base C v; rw [integral_const_mul, integral_indicator cells_closed.measurableSet, setIntegral_const, smul_eq_mul]; rw [spike_pos hr]; ring
end YM.Pert.Cellular
