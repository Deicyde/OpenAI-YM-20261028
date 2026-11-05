import YM.Extra.SOURCE_HISTORIES.Charts

/-!
# Cost of the actual charts. Obstruction to extracting raw terminals.

In
particular at *fixed m* lengths neither side costs a mesh- or period-
dependent factor.

Raw `Q_N`, very different, contains a column which
diverges on ANY sequence of sufficient cutoffs when d>0.

Preserve the a^d
unit-scaling and track also the inevitable inverse bound cost as m grows;
no convergence claim moving m to infinity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Charts
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion Extraction
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (C : Family G) (h : C.Makes) (d N p m : ℕ)

include h in
lemma raw_unit (hr : C.ref d≤N) : (C.factory d N p).terminal (C.labels.level d).e0 =
    ((C.S.a N : ℂ)^d)⁻¹ • C.refUnit d := by
  have he := terminal_unit_vec C h d N p hr
  have hx : (C.factory d N p).terminal (unitVec (C.labels.level d) C.path N)=C.refUnit d := by
    rw [← he, LinearEquiv.apply_symm_apply]
  rw [unitVec,map_smul] at hx; rw [← hx,smul_smul]; simp [(C.S.a_pos N).ne']

include h in
theorem raw_escapes (hd : 0 < d) : ∀ z : ℝ, ∀ᶠ N : ℕ in atTop, ∀ p,
    z ≤ ‖(C.factory d N p).terminal (C.labels.level d).e0‖ := by
  have hv : Tendsto (fun N => ((C.S.a N)^d)⁻¹) atTop atTop := by
    have he : Tendsto (fun N => (C.S.a N)⁻¹) atTop atTop := by
      unfold Schedule.a; simp only [inv_inv]; exact tendsto_natCast_atTop_atTop.comp C.S.den_strict.tendsto_atTop
    simpa only [Function.comp_def,inv_pow] using (tendsto_pow_atTop hd.ne').comp he
  have hh : 0 < ‖C.refUnit d‖ := norm_pos_iff.mpr (by
    unfold Family.refUnit unitVec
    rw [smul_ne_zero_iff]; exact ⟨pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'),fun h => by
      have H := congr_fun h 0; simp [Frame.e0] at H⟩)
  intro z
  filter_upwards [(hv.atTop_mul_const hh).eventually_ge_atTop z, eventually_ge_atTop (C.ref d)] with N hN hr p
  rw [raw_unit C h d N p hr,norm_smul,norm_inv,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le]
  exact hN

include h in
/-- Even trying to include the Q matrices among auxiliary finite-data
mesh limits (at fixed p) fails for the actual readout. -/
theorem forbids (f : ℕ → ℕ) (hr : Tendsto f atTop atTop) (hd : 0 < d) (x : C.label d) :
    ¬ Tendsto (fun i => (C.factory d (f i) p).terminal (C.labels.level d).e0) atTop (𝓝 x) := by
  intro H
  have ht := H.norm.eventually (gt_mem_nhds (show ‖x‖<‖x‖+1 by linarith))
  have hs := hr.eventually (raw_escapes C h d hd (‖x‖+1))
  obtain ⟨i,hi,hj⟩ := ht.and hs |>.exists
  exact lt_irrefl _ ((hj p).trans_lt hi)

-- Totalized chart bounds, using the library *exact* sum-of-column prices.
def ingress := Real.exp (Work.D01.columnLogs C.path.levels m)
def outgress := Real.exp (d*C.S.scale m + Work.D01.columnLogs C.path.levels m)

lemma ingress_one : 1 ≤ ingress C m := Real.one_le_exp (Work.D01.columnLogs_nonneg _ _)
lemma outgress_one : 1 ≤ outgress C d m := Real.one_le_exp (add_nonneg
  (mul_nonneg (Nat.cast_nonneg _) (Shoot.scale_nn C.path.levels m)) (Work.D01.columnLogs_nonneg _ _))

theorem incoming (v : C.label d) : (C.labels.level d).coeffSize (window C h d m N p v) ≤
    ingress C m * (C.labels.level d).coeffSize v := by
  by_cases hs : C.ref d≤m ∧ m≤N
  · rw [peek C h _ _ _ _ hs.1 hs.2]
    exact Work.D01.back_budget C h _ hs.1 hs.2
  rw [window,dif_neg hs]
  exact le_mul_of_one_le_left (Work.G08.size_nonneg ..) (ingress_one C m)

private lemma outgress_step : outgress C d (m+1) = outgress C d m *
    ((C.path.levels.params (m+1)).columns*((C.S.block m).val:ℝ)^d) := by
  unfold outgress
  have hm := (C.path.levels.params (m+1)).columns_ge
  have hp : 0 < (C.path.levels.params (m+1)).columns := zero_lt_one.trans_le hm
  have hv : 0 < ((C.S.block m).val:ℝ) := Nat.cast_pos.mpr (C.S.block m).property
  rw [Schedule.scale_succ, Work.D01.columnLogs_succ]
  simp only [mul_add, Real.exp_add,Real.exp_nat_mul,Real.exp_log hp,Real.exp_log hv]; ring

theorem outer_charge (v : C.label d) : (C.labels.level d).coeffSize ((window C h d m N p).symm v) ≤
    outgress C d m * (C.labels.level d).coeffSize v := by
  let F := C.labels.level d
  by_cases hs : C.ref d≤m ∧ m≤N
  · rcases hs with ⟨hr, hm⟩
    have hd : C.ref d≤N := le_trans hr hm
    have hx (i : ℕ) (he : C.ref d ≤ i) (ht : i ≤ N) (v : C.label d) :
        F.coeffSize v ≤ outgress C d i * F.coeffSize (window C h d i N p v) := by
      induction i, he using Nat.le_induction with
      | base =>
        rw [ref_chart C h d N p hd]
        exact le_mul_of_one_le_left (Work.G08.size_nonneg ..) (outgress_one C _ _)
      | succ i he ih =>
        refine le_trans (ih (i.le_succ.trans ht)) ?_
        rw [peek C h d N p i he (i.le_succ.trans ht), peek C h d N p (i+1) (he.trans i.le_succ) ht,
          outgress_step, mul_assoc]
        exact mul_le_mul_of_nonneg_left ((h.calibrated d N p hd).front i he ht _) (zero_le_one.trans (outgress_one C _ _))
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx m hr hm ((window C h d m N p).symm v)
  rw [window,dif_neg hs]
  exact le_mul_of_one_le_left (Work.G08.size_nonneg ..) (outgress_one C _ _)





include h in
/-- Even in continuum-comparison language the inverse isn't uniformly
subexponential in m. It has to scale back the units. -/
theorem inverse_unit (hr : C.ref d ≤ m) (hm : m ≤ N) : ‖(window C h d m N p).symm (C.labels.level d).e0‖ =
    ((C.S.a m)^d)⁻¹ * ‖C.refUnit d‖ := by
  let W := window C h d m N p
  have hv : W.symm (unitVec (C.labels.level d) C.path m)=C.refUnit d := by
    rw [← chart_unit C h d N p m hr hm]; exact ContinuousLinearEquiv.symm_apply_apply ..
  have hz : (C.S.a m)^d≠0 := pow_ne_zero _ (C.S.a_pos _).ne'
  change ‖W.symm _‖=_
  conv_rhs => rw [← hv]
  rw [unitVec,map_smul,norm_smul,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le,
    ← mul_assoc,inv_mul_cancel₀ hz,one_mul]

end YM.Extra.Histories.Charts
