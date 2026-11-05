import YM.Push.PRICE_COMPILER.Rates
import YM.Work.E09.Scales

/-!
# Loop cap handoff and delay

E eq:b2loop , gate . The $L^4$ cost can be large;
take `theta` only after L and before coupling delays. And use a small
factor (pre-L power) multiplying the inherited estimate, NOT trying to
afford a `C_L` *multiplier on the cap* by this delay.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG Wilson RG.Supply Pressure
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-- The stipulated monitor `exp ((log (log x))^2)`, including at first m.
All delay claims use it eventually in `x` for each fixed shift `k`. -/
abbrev mon := Vac.Numbers.P

lemma mon_ge (x : ℝ) : 1 ≤ mon x := Real.one_le_exp (sq_nonneg _)
lemma mon_pos (x : ℝ) : 0 < mon x := Real.exp_pos _
lemma mon_deep : Tendsto mon atTop atTop := by
  refine Real.tendsto_exp_atTop.comp ?_
  exact (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)

lemma mon_ratio (k : ℝ) : Tendsto (fun x : ℝ => mon (x+k) / mon x) atTop (𝓝 1) := by
  have hl := Work.E09.temp_ratio k
  have hb : Tendsto (fun x : ℝ => (x+k)/x) atTop (𝓝 1) := by
    have he := (tendsto_const_nhds (f:=atTop) (x:=k)).div_atTop (tendsto_id (α:=ℝ) (x:=atTop))
    refine Tendsto.congr' ?_ (show Tendsto (fun x : ℝ => 1 + k/x) atTop (𝓝 1) from by simpa using he.const_add 1)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; field_simp
  have h : Tendsto (fun x : ℝ => Real.sqrt ((x+k)/x) * (temp (x+k)/temp x)) atTop (𝓝 1) := by
    simpa using hb.sqrt.mul hl
  refine Tendsto.congr' ?_ h
  have ht : Tendsto (fun x : ℝ => x+k) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  filter_upwards [eventually_gt_atTop (0:ℝ), ht.eventually (eventually_gt_atTop 0)] with x hx he
  change 0 < x+k at he
  rw [Real.sqrt_div he.le]
  have hs := Real.sqrt_pos.mpr he
  have hy := Real.sqrt_pos.mpr hx
  have hg (x : ℝ) : temp x = (Real.sqrt x)⁻¹ * mon x := rfl
  rw [hg,hg]
  field_simp

lemma mon_power_ratio (k r : ℝ) : Tendsto (fun x : ℝ => mon (x+k) ^ r / mon x ^ r) atTop (𝓝 1) := by
  have hz : Tendsto (fun x : ℝ => (mon (x+k)/ mon x) ^ r) atTop (𝓝 1) := by
    simpa using (mon_ratio k).rpow_const (p:=r) (by simp)
  exact hz.congr fun x => Real.div_rpow (mon_pos _).le (mon_pos _).le r

lemma mon_power_deep {r : ℝ} (hr : 0 < r) : Tendsto (fun x => mon x ^ r) atTop atTop :=
  (tendsto_rpow_atTop hr).comp mon_deep

variable {G : Gauge} {p : Sheet G} {D : Rolls p} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}

structure Grows (t : LoopPrices) (T : Protection D) (j i : ℕ) (x : ℝ) : Prop where
  transfer : mon (betaF G x (D.L j)) ^ (T.theta j) ≤ 2 * mon x ^ (T.theta i)
  seed : t.add j i * ((D.L j).val:ℝ)^4 ≤ mon x ^ (T.theta i)

lemma Grows.late (t : LoopPrices) (T : Protection D) {j i : ℕ} (h : i ≤ j) : ∀ᶠ x in atTop, Grows t T j i x := by
  let k := G.slopeConstant * Real.log (D.L j).val
  have hg := (mon_power_ratio k (T.theta j)).eventually (ge_mem_nhds (show (1:ℝ)<2 by norm_num))
  have ht := (mon_power_deep (T.pos i)).eventually_ge_atTop (t.add j i * ((D.L j).val:ℝ)^4)
  filter_upwards [hg,ht] with x hx he
  refine ⟨?_,he⟩
  exact ((div_le_iff₀ (Real.rpow_pos_of_pos (mon_pos _) _)).mp hx).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (mon_ge x) (T.dec h)) (by norm_num))

/-- Entrance request for all possible uses, AFTER θ. -/
theorem can_delay_loop (t : LoopPrices) (T : Protection D) (e : ℕ → ℝ) :
    ∃ F : ℕ → ℝ, Monotone F ∧ e ≤ F ∧ ∀ j x, F j ≤ x → ∀ i, StepStages j i → Grows t T j i x := by
  apply collect_upper e (fun j x => ∀ i, StepStages j i → Grows t T j i x)
  intro j
  exact eventually_transitions _ _ _ fun _ hi => Grows.late t T hi.1

/-- Use Grows for a loopCap invocation across a genuine calendar edge.
Handles within-stage continuation. -/
theorem buys_loop (t : LoopPrices) (a : Levels G) (h : Paid I a) (m : ℕ) :
    let j := a.clock.J (m+1)
    let i := a.clock.J m
    let L := a.S.block m
    Grows t T j i (a.clock.hatBeta m) →
    t.send j i / (L.val:ℝ)^2 ≤ 1/4 →
      t.cost j i (L.val:ℝ) (a.clock.loopCap (m+1)) ≤ a.clock.loopCap m := by
  intro j i L hg hq
  have he := h.theta
  let x := a.clock.hatBeta m
  let y := a.clock.hatBeta (m+1)
  have hu : a.clock.loopCap (m+1) = 2 * mon y ^ T.theta j := by rw [Calendar.loopCap, he]; rfl
  have hx : a.clock.loopCap m = 2 * mon x ^ T.theta i := by rw [Calendar.loopCap, he]; rfl
  have hb : y=betaF G x (D.L j) := beta_eq h m
  have ht : t.add j i * (L.val:ℝ)^ (4:ℕ) ≤ mon x ^ T.theta i := by
    rw [show L = D.L j from block_eq h m]
    exact hg.seed
  have hy : mon y ^ T.theta j ≤ 2 * mon x ^ T.theta i := hb.symm ▸ hg.transfer
  have hw : (0:ℝ) ≤ 2 * mon y ^ T.theta j := mul_nonneg (by norm_num) (Real.rpow_nonneg (mon_pos _).le _)
  have hk := mul_le_mul_of_nonneg_right hq hw
  unfold LoopPrices.cost
  rw [hu,hx]; linarith

lemma cap_ge (a : Levels G) (m : ℕ) : 2 ≤ a.clock.loopCap m := le_mul_of_one_le_right (by norm_num)
  (Real.one_le_rpow (mon_ge _) (a.fits.thetaRange m).1.le)
end YM.Push.PriceCompiler
