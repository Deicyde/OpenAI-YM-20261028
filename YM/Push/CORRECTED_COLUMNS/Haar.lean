import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import YM.Gauge.Size

/-!
# Side calculation for the terminal plaquette elimination

For the *actual* `probHaar` and normalized Frobenius chord, a relative
estimate – no charts or connectedness needed. This avoids having to prove
sharp Lie-*dimension* powers on both numerator and denominator in the last
step of the detector estimate (cf. ). Paying a per-site power from a
non-sharp lower bound on the denominator alone could be disastrous.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected
open MeasureTheory Set Function Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators ENNReal

section

-- Relative finite-dimensional estimate, in AMBIENT dimension.
private theorem pack_aux {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y : V → E} {s R : ℝ} (hs : 0 < s) (hr : 0 ≤ R) (p : Finset V)
    (hc : ∀ i ∈ p, ‖Y i‖ ≤ R)
    (hp : (p:Set V).Pairwise (fun i j => s < ‖Y i - Y j‖)) :
    p.card ≤ (1 + 2*R/s)^Module.finrank ℝ E := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  letI : MeasurableSpace E := borel _
  letI : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := Measure.addHaar
  haveI : Measure.IsAddHaarMeasure μ := by dsimp [μ]; infer_instance
  let B (i : V) := Metric.ball (Y i) (s/2)
  have hj : PairwiseDisjoint (p : Set V) B := by
    intro i hi j hj h
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h1 := norm_sub_le_norm_sub_add_norm_sub (Y i) x (Y j)
    have h2 : ‖Y i-x‖ < s/2 := by rw [norm_sub_rev]; simpa only [B,Metric.mem_ball,dist_eq_norm] using hx
    have h3 : ‖x-Y j‖ < s/2 := by simpa only [B, Metric.mem_ball, dist_eq_norm] using hy
    have h4 : s < ‖Y i-Y j‖ := hp hi hj h
    linarith
  have hb : (⋃ i ∈ p, B i) ⊆ Metric.ball (0:E) (R+s/2) := by
    refine iUnion_subset fun i => iUnion_subset fun hi => ?_
    intro x hx
    have H : ‖x-Y i‖ < s/2 := by simpa only [B, Metric.mem_ball, dist_eq_norm] using hx
    have H' := norm_sub_le_norm_sub_add_norm_sub x (Y i) 0
    rw [Metric.mem_ball, dist_zero_right]
    simp only [sub_zero] at H'
    linarith [hc i hi]
  have h0 (a : E) (b : ℝ) : μ (Metric.ball a b) ≠ ⊤ := measure_ball_lt_top.ne
  let d := Module.finrank ℝ E
  let D := μ.real (Metric.ball 0 1)
  have hD : 0 < D := ENNReal.toReal_pos
    (Measure.IsOpenPosMeasure.open_pos _ Metric.isOpen_ball (Metric.nonempty_ball.mpr zero_lt_one)) (h0 _ _)
  have he (a : E) (r : ℝ) (hr : 0 < r) : μ.real (Metric.ball a r)=r^d*D := by
    unfold D; rw [measureReal_def,Measure.addHaar_ball_of_pos μ _ hr,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]; rfl
  have hB := measureReal_mono (μ:=μ) hb (h0 _ _)
  rw [measureReal_biUnion_finset hj (fun i _ => Metric.isOpen_ball.measurableSet) (fun i _ => h0 _ _)] at hB
  have hx i : μ.real (B i)=(s/2)^d*D := he _ _ (by positivity)
  simp_rw [hx, he _ _ (show 0 < R+s/2 by positivity)] at hB
  simp only [Finset.sum_const,nsmul_eq_mul] at hB
  apply le_of_mul_le_mul_right (a := (s/2)^d*D) ?_ (by positivity)
  refine hB.trans_eq ?_
  rw [← mul_assoc, ← mul_pow]
  congr 2
  field_simp
  ring
end

attribute [local instance] Gauge.frobInner
variable (G : Gauge)

-- Maximal net using the same chord normalization on the left translates.
theorem shell_ratio {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    G.probHaar.real (G.shell R) ≤ (1+2*R/r)^Module.finrank ℝ G.Mat * G.probHaar.real (G.shell r) := by
  classical
  let D (i j : G.El) := ‖G.mat i-G.mat j‖
  let γ := G.colorScale
  have hg : 0 < γ := G.colorScale_pos
  let C := G.shell R
  let Pack (p : Finset G.El) : Prop := (∀ i ∈ p, i ∈ C) ∧ (p : Set G.El).Pairwise fun i j => r*γ < D i j
  have hx (p : Finset G.El) (H : Pack p) : (p.card:ℝ) ≤ (1+2*R/r)^Module.finrank ℝ G.Mat := by
    have ha (i) (h : i ∈ p) : ‖G.mat i-1‖ ≤ R*γ := (div_le_iff₀ hg).mp (show G.chord i ≤ R from H.1 i h)
    let Y (i : G.El) := G.mat i-1
    have hp := pack_aux (Y:=Y) (mul_pos hr hg) (mul_nonneg hR hg.le) p ha (by
      intro i hi j hj h
      have hv : Y i-Y j=G.mat i-G.mat j := by unfold Y; abel
      rw [hv]; exact H.2 hi hj h)
    apply hp.trans_eq
    field_simp
  have cover : ∃ p : Finset G.El, Pack p ∧ ∀ x ∈ C, ∃ i ∈ p, D i x ≤ r*γ := by
    by_contra he
    have hl p (hp : Pack p) : ∃ x ∈ C, ∀ i ∈ p, r*γ < D i x := by
      push Not at he
      exact he p hp
    have hv (n : ℕ) : ∃ p : Finset G.El, p.card = n ∧ Pack p := by
      induction n with
      | zero => exact ⟨∅,Finset.card_empty,by simp [Pack]⟩
      | succ n ih =>
        obtain ⟨p,he,H⟩ := ih
        obtain ⟨x,hm,hw⟩ := hl p H
        have hh : x∉p := by
          intro a
          have h0 := hw x a; simp only [D,sub_self,norm_zero] at h0
          exact (mul_pos hr hg).not_gt h0
        refine ⟨insert x p,by rw [Finset.card_insert_of_notMem hh,he],?_,?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with h|h
          · exact h ▸ hm
          exact H.1 i h
        intro i hi j hj h
        rcases Finset.mem_insert.mp hi with rfl|hiA <;> rcases Finset.mem_insert.mp hj with rfl|hj
        · exact (h rfl).elim
        · unfold D; rw [norm_sub_rev]; exact hw j hj
        · exact hw i hiA
        exact H.2 hiA hj h
    obtain ⟨n,hn⟩ := exists_nat_gt ((1+2*R/r)^Module.finrank ℝ G.Mat)
    obtain ⟨p,h,hp⟩ := hv n
    exact hn.not_ge (h ▸ hx p hp)
  obtain ⟨p,hp,h⟩ := cover
  let S (i : G.El) := (fun x : G.El => i⁻¹*x) ⁻¹' G.shell r
  have hs : C ⊆ ⋃ i∈p, S i := by
    intro x hm; obtain ⟨i,hi,hx⟩ := h x hm
    refine mem_iUnion₂.mpr ⟨i,hi,?_⟩
    change G.chord (i⁻¹*x) ≤ r
    apply (div_le_iff₀ hg).mpr
    rw [G.mat_mul, ← G.mat_one,← inv_mul_cancel i, G.mat_mul,← mul_sub,
      Gauge.mul_frob_eq _ _ (G.mat_star_mul _),norm_sub_rev]
    exact hx
  have hw (i) : G.probHaar.real (S i)=G.probHaar.real (G.shell r) := by
    have he := (measurePreserving_mul_left G.probHaar i⁻¹).measure_preimage (G.shell_meas r).nullMeasurableSet
    exact congr_arg ENNReal.toReal he
  refine (measureReal_mono (μ:=G.probHaar) hs (measure_ne_top _ _)).trans ((measureReal_biUnion_finset_le p S).trans ?_)
  simp_rw [hw]
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hx p hp) (by positivity)

/-- One-link integrable upper weight; coefficient `c>0` with normalized chord. -/
def link (c r : ℝ) (x : G.El) := Real.exp (-c*(G.chord x/r))

lemma link_cont (c r : ℝ) : Continuous (link G c r) := by unfold link; fun_prop
lemma link_nonneg (c r : ℝ) (x : G.El) : 0 ≤ link G c r x := (Real.exp_pos _).le
lemma link_le (c r : ℝ) (hc : 0 < c) (hr : 0 < r) (x : G.El) : link G c r x ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (div_nonneg (G.chord_nonneg _) hr.le))

-- economical overshoot j=floor(chord/r); shell((j+1) r)/shell r ≤ (2*j+3)^D ≤ (3*(j+1))^D.
def tariffs (c : ℝ) (j : ℕ) : ℝ := (3*((j:ℝ)+1))^Module.finrank ℝ G.Mat * Real.exp (-c*j)
def multiplier (c : ℝ) : ℝ := 1 + ∑' j, tariffs G c j
lemma toll_pos (c : ℝ) (j : ℕ) : 0 ≤ tariffs G c j := by unfold tariffs; positivity
lemma fits_toll {c : ℝ} (hc : 0 < c) : Summable (tariffs G c) := by
  let d := Module.finrank ℝ G.Mat
  have h : Summable fun j : ℕ => (j:ℝ)^d * Real.exp (-c*j) := Real.summable_pow_mul_exp_neg_nat_mul d hc
  have hp := (summable_nat_add_iff 1).2 h
  refine (hp.mul_left (3^d * Real.exp c)).congr ?_
  intro j
  dsimp only [tariffs]
  push_cast
  rw [mul_pow]
  have H : Real.exp (-c*j) = Real.exp c * Real.exp (-c*((j:ℝ)+1)) := by rw [← Real.exp_add]; congr 1; ring
  rw [H]; change _ = 3^d * _ * _; ring

lemma mult_ge (c : ℝ) : 1 ≤ multiplier G c := le_add_of_nonneg_right (tsum_nonneg (toll_pos G c))

/-- The bound needed against the *same* small-link probability used for the
vacuum lower bound. This one has no factor depending on `1/r`, even for
very small `r`. -/
theorem link_est (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    (∫ x, link G c r x ∂G.probHaar) ≤ multiplier G c * G.probHaar.real (G.shell r) := by
  let P (j : ℕ) := G.shell (((j:ℝ)+1)*r)
  let f (j : ℕ) := (P j).indicator fun _ => Real.exp (-c*j)
  have hi j : Integrable (f j) G.probHaar := (integrable_const _).indicator (G.shell_meas _)
  let b := ⌊2/r⌋₊ + 1
  let p := Finset.range b
  have hs x : link G c r x ≤ ∑ j ∈ p, f j x := by
    let j := ⌊G.chord x/r⌋₊
    have hR : G.chord x/r ≤ 2/r := div_le_div_of_nonneg_right (G.chord_le_two _) hr.le
    have hj : j ∈ p := Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_le_floor hR))
    have hP : x ∈ P j := ((div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (G.chord x/r))).le
    have hf (i : ℕ) : 0 ≤ f i x := by
      unfold f
      by_cases he : x ∈ P i
      · rw [indicator_of_mem he]; exact (Real.exp_pos _).le
      rw [indicator_of_notMem he]
    refine le_trans ?_ (Finset.single_le_sum (f:=fun j => f j x) (fun i _ => hf i) hj)
    unfold f; rw [indicator_of_mem hP]; apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (Nat.floor_le (div_nonneg (G.chord_nonneg _) hr.le)) (by linarith)
  have hf (j : ℕ) : (∫ x, f j x ∂G.probHaar) ≤ tariffs G c j * G.probHaar.real (G.shell r) := by
    unfold f
    rw [integral_indicator (G.shell_meas _)]; simp only [setIntegral_const, smul_eq_mul]
    let D := Module.finrank ℝ G.Mat
    have h0 : G.probHaar.real (P j) ≤ (3*((j:ℝ)+1))^D * G.probHaar.real (G.shell r) := by
      refine (shell_ratio G hr (by positivity : 0 ≤ ((j:ℝ)+1)*r)).trans ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      refine pow_le_pow_left₀ (by positivity) ?_ _
      field_simp
      linarith [(Nat.cast_nonneg j : 0 ≤ (j:ℝ))]
    apply (mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le).trans_eq
    unfold tariffs; ac_rfl
  refine (integral_mono ((link_cont G _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (integrable_finsetSum p (fun j _ => hi j)) hs).trans ?_
  rw [integral_finsetSum _ (fun j _ => hi j)]
  refine (Finset.sum_le_sum (fun j _ => hf j)).trans ?_
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact ((fits_toll G hc).sum_le_tsum _ (fun i _ => toll_pos G c i)).trans (le_add_of_nonneg_left zero_le_one)
end YM.Push.Corrected
