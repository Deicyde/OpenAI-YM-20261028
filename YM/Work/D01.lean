import YM.Bid.Drops

/-!
# Top coefficient budget (D01)

One frame at a fixed degree, one origin calibration. The product-of-columns
estimate bounds the pullback of the reference label in **that factory**, on
all periods. This is a top *coordinate* budget; no discrepancy, remainder
estimate on a new presentation, or calibration producer is claimed here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.D01

open Filter
open scoped Topology BigOperators

variable {G : Gauge}

/-- Pad the backwards cost with all column costs even before the reference. -/
def columnLogs (a : RG.Levels G) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, Real.log (a.params (i+1)).columns

lemma columnLogs_nonneg (a : RG.Levels G) (m : ℕ) : 0 ≤ columnLogs a m :=
  Finset.sum_nonneg fun i _ => Real.log_nonneg (a.params (i+1)).columns_ge

lemma columnLogs_succ (a : RG.Levels G) (m : ℕ) :
    columnLogs a (m+1) = columnLogs a m + Real.log (a.params (m+1)).columns :=
  Finset.sum_range_succ _ _

/-- The pre-L prices in this calendar suffice for subscale cost. Use the
same head/tail reasoning as for the beta drift in `Shoot.trajectory`. -/
theorem columnLogs_le (a : RG.Levels G) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ N in atTop, columnLogs a N ≤ ε * a.S.scale N := by
  have hd : Tendsto (fun i : ℕ => ((a.clock.J (i+1):ℝ)^2)⁻¹) atTop (𝓝 0) := by
    have ht := a.fits.deep.comp (tendsto_add_atTop_nat 1)
    exact tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (n := 2) (by decide)).comp (tendsto_natCast_atTop_atTop.comp ht))
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hd.eventually (ge_mem_nhds (half_pos he)))
  have tail (i : ℕ) (hi : k ≤ i) :
      columnLogs a i ≤ columnLogs a k + (ε/2) * (a.S.scale i - a.S.scale k) := by
    induction i,hi using Nat.le_induction with
    | base => rw [sub_self, mul_zero, add_zero]
    | succ i hi ih =>
      let p := a.params (i+1)
      have hL : 0 < Real.log (a.S.block i).val := Real.log_pos (by
        exact_mod_cast (show 1 < (a.S.block i).val from lt_of_lt_of_le (by norm_num) (a.S.block_large i)))
      have hcost : Real.log
          (1 + p.paths + p.width⁻¹ + p.columns + p.clip.relaxation + p.supportExponent) /
            Real.log (a.S.block i).val ≤ ((a.clock.J (i+1):ℝ)^2)⁻¹ := a.fits.logCost i
      have hstep : Real.log (a.params (i+1)).columns ≤ (ε/2) * Real.log (a.S.block i).val := by
        apply le_trans _ ((div_le_iff₀ hL).mp (hcost.trans (show _ ≤ ε/2 from hk i hi)))
        change Real.log p.columns ≤ _
        exact Real.log_le_log (lt_of_lt_of_le zero_lt_one p.columns_ge) (by
          linarith only [p.paths_pos, inv_pos.mpr p.width_pos, p.clip.radius_pos, p.price_pos])
      rw [columnLogs_succ, Schedule.scale_succ]
      linarith only [ih, hstep]
  filter_upwards [eventually_ge_atTop k,
    (a.S.divergent.const_mul_atTop (half_pos he)).eventually_ge_atTop (columnLogs a k)]
    with i hi hhead
  have hpre : columnLogs a k ≤ (ε/2) * a.S.scale i := hhead
  linarith only [tail i hi, hpre, mul_nonneg he.le (RG.Shoot.scale_nn a k)]

/-- Iterate `back` for the very same entry trajectory at `(d,N,p)`. -/
theorem back_budget (C : Family G) (h : C.Makes) {d N p m : ℕ}
    (x : C.label d) (hr : C.ref d ≤ m) (hm : m ≤ N) :
    let T := C.factory d N p
    let Z := C.labels.level d
    Z.coeffSize (T.entries m (T.terminal.symm x)).x ≤
      Real.exp (columnLogs C.path.levels m) * Z.coeffSize x := by
  intro T Z
  induction m,hr using Nat.le_induction with
  | base =>
    rw [show (T.entries (C.ref d) (T.terminal.symm x)).x = x from C.normalized h hm x]
    exact le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Real.one_le_exp (columnLogs_nonneg _ _))
  | succ m hr ih =>
    have ht := h.calibrated d N p (hr.trans (le_trans (Nat.le_succ m) hm))
    have hpos : 0 < (C.path.levels.params (m+1)).columns :=
      lt_of_lt_of_le zero_lt_one (C.path.levels.params _).columns_ge
    calc
      _ ≤ (C.path.levels.params (m+1)).columns * Z.coeffSize (T.entries m (T.terminal.symm x)).x :=
        ht.back m hr hm _
      _ ≤ (C.path.levels.params (m+1)).columns *
          (Real.exp (columnLogs C.path.levels m) * Z.coeffSize x) :=
        mul_le_mul_of_nonneg_left (ih (le_trans (Nat.le_succ m) hm)) hpos.le
      _ = _ := by rw [columnLogs_succ, Real.exp_add, Real.exp_log hpos]; ring

/-- Note the single cardinal factor (sup-norm vs the l1 budget). Uniform
in p and the vector in the ball, needs a fixed degree and radius only. -/
theorem terminal_ball (C : Family G) (h : C.Makes) (d : ℕ) (A ε : ℝ) (he : 0 < ε) :
    ∀ᶠ N in atTop, ∀ p, ∀ x : C.label d, ‖x‖ ≤ A →
      ‖(C.factory d N p).terminal.symm x‖ ≤ Real.exp (ε * C.S.scale N) := by
  let Z := C.labels.level d
  have hc := columnLogs_le C.path.levels (ε/2) (half_pos he)
  have hs : Tendsto (fun N => Real.exp ((ε/2) * C.S.scale N)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (C.S.divergent.const_mul_atTop (half_pos he))
  filter_upwards [hc, hs.eventually_ge_atTop ((Fintype.card Z.Index:ℝ) * A),
    eventually_ge_atTop (C.ref d)] with N hN ha hr
  intro p x hx
  let T := C.factory d N p
  have hw : Z.coeffSize x ≤ Real.exp ((ε/2) * C.S.scale N) := calc
    _ ≤ (Fintype.card Z.Index:ℝ) * ‖x‖ := by
      simpa only [Labels.Frame.coeffSize, nsmul_eq_mul] using Pi.sum_norm_apply_le_norm (G := fun _ : Z.Index => ℂ) x
    _ ≤ (Fintype.card Z.Index:ℝ) * A := mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ _ := ha
  have hb : Z.coeffSize (T.terminal.symm x) ≤ Real.exp (columnLogs C.path.levels N) * Z.coeffSize x := by
    have hk : Z.coeffSize (T.entries N (T.terminal.symm x)).x ≤ _ :=
      back_budget C h (p := p) x hr le_rfl
    rw [show (T.entries N (T.terminal.symm x)).x = T.terminal.symm x from
      (h.calibrated d N p hr).bare_coord _] at hk
    exact hk
  change ‖T.terminal.symm x‖ ≤ _
  have hnn : 0 ≤ Z.coeffSize x := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc
    _ ≤ Z.coeffSize (T.terminal.symm x) := by
      apply (pi_norm_le_iff_of_nonneg (show 0 ≤ Z.coeffSize (T.terminal.symm x) from
        Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
      intro i
      exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ _ := hb.trans (calc
      _ ≤ Real.exp ((ε/2) * C.S.scale N) * Real.exp ((ε/2) * C.S.scale N) :=
        mul_le_mul (Real.exp_le_exp.mpr hN) hw hnn (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; ring_nf)

theorem answer : YM.Bid.D01 := by
  intro G C h d F w hw ε he
  obtain ⟨A,hA⟩ := hw
  have hb := F.mesh.cofinal.eventually (terminal_ball C h d A ε he)
  unfold Extraction.Order.late at hA ⊢
  filter_upwards [hA] with k hk
  filter_upwards [hk, hb] with j hj hj'
  exact hj' (F.per k) _ hj

end YM.Work.D01
