import YM.Analysis.Polydisc
import YM.Bid.Corners

/-!
# From the strict-height testing formula to half-space support (absolute frequency variables)

Use monotone, not necessarily *strictly* monotone heights to separate. Run up that ray with a
fixed additive strict offset, on which the position-space bound from `Breathes` is uniform. When
localized in the separating patch, the exponentially weighted frequency test in `during` now
decays in Schwartz topology.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Work.C06

open Filter Set Function Distribution MeasureTheory Boundary
open scoped Topology BigOperators ContDiff InnerProductSpace

variable {n : ℕ}

private lemma exp_bound (L : Points n →L[ℝ] ℝ) (j : ℕ) (x : Points n) :
    ‖iteratedFDeriv ℝ j (Real.exp ∘ L) x‖ ≤ Real.exp (L x) * ‖L‖ ^ j := by
  rw [L.iteratedFDeriv_comp_right (show ContDiff ℝ (j : ℕ) Real.exp from Real.contDiff_exp)
    x (i := j) le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  simp [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos (L x)).le]

private lemma support_lifts (u : Points n) (f : Joint n) (hf : HasCompactSupport ⇑f) :
    tsupport (lifts u f hf) ⊆ tsupport f :=
  tsupport_mul_subset_right

/-- Negative frequency patch with unit margin (rescale the direction to obtain this).
All orders of seminorm decay; `lifts` only has to be formed for compactly supported tests.
-/
lemma lift_falls (u : Points n) (f : Joint n) (hf : HasCompactSupport ⇑f)
    (h : ∀ x ∈ tsupport f, inner ℝ u x ≤ -1) :
    Tendsto (fun t : ℝ => lifts (t • u) f hf) atTop (𝓝 0) := by
  apply (Probe.tendN ..).2
  intro i j ε hε
  let L : Points n →L[ℝ] ℝ := innerSL ℝ u
  let b (l : ℕ) (t : ℝ) := (j.choose l : ℝ) * (Real.exp (-t) * (t * ‖L‖)^l) *
    Probe.size i (j-l) f
  have hterm (l : ℕ) : Tendsto (b l) atTop (𝓝 0) := by
    have he := (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero l).mul_const (‖L‖^l)).const_mul
      (j.choose l : ℝ)).mul_const (Probe.size i (j-l) f)
    simp only [zero_mul, mul_zero] at he
    refine he.congr fun t => ?_
    dsimp only [b]
    rw [mul_pow]; ring
  have hh : Tendsto (fun t => ∑ l ∈ Finset.range (j+1), b l t) atTop (𝓝 0) := by
    simpa using (tendsto_finsetSum (Finset.range (j+1)) (fun l _ => hterm l))
  filter_upwards [eventually_ge_atTop (0 : ℝ), hh.eventually (gt_mem_nhds hε)] with t ht he
  rw [sub_zero]
  have hnn : 0 ≤ ∑ l ∈ Finset.range (j+1), b l t :=
    Finset.sum_nonneg fun l _ => by dsimp only [b, Probe.size]; positivity
  refine lt_of_le_of_lt ((lifts (t • u) f hf).seminorm_le_bound ℂ i j hnn ?_) he
  intro x
  by_cases hx : x ∈ tsupport f
  · let A := t • L
    have hA : A x ≤ -t := calc
      A x = t * inner ℝ u x := rfl
      _ ≤ t * (-1) := mul_le_mul_of_nonneg_left (h x hx) ht
      _ = -t := by ring
    have hn : ‖A‖ = t * ‖L‖ := by simp only [A, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    have hexp (l : ℕ) : ‖iteratedFDeriv ℝ l (Real.exp ∘ A) x‖ ≤
        Real.exp (-t) * (t * ‖L‖)^l :=
      (exp_bound A l x).trans (by rw [← hn]; gcongr)
    have hs : ⇑(lifts (t • u) f hf) = fun w => (Real.exp ∘ A) w • f w := by
      funext w
      change lifts (t • u) f hf w = Real.exp (t * inner ℝ u w) • f w
      rw [rises, Complex.real_smul, Complex.ofReal_exp, real_inner_smul_left]
    rw [hs]
    have hc : ContDiff ℝ ∞ (Real.exp ∘ A) := Real.contDiff_exp.comp A.contDiff
    refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hc (f.smooth ⊤) x
      (n := j) (by exact_mod_cast le_top)) (by positivity)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [mul_left_comm]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hexp l) (by positivity))
      (SchwartzMap.le_seminorm ℂ i (j-l) f x) (by positivity) (by positivity)
  · rw [Probe.vanish_j (x := x) _ _ ((notMem_tsupport_iff_eventuallyEq).1
      (fun H => hx (support_lifts (t • u) f hf H))), norm_zero, mul_zero]
    exact hnn

private lemma sunrise_smul {y : Heights n} (hy : y ∈ sunrise n) {t : ℝ} (ht : 0 ≤ t) :
    t • y ∈ sunrise n := fun _ _ h => mul_le_mul_of_nonneg_left (hy h) ht

private lemma dawn_add (x y : Heights n) : dawn (x+y) = dawn x + dawn y := by
  ext1 i
  apply Mink.ext_by <;> simp [dawn, place]

private lemma dawn_smul (x : Heights n) (t : ℝ) : dawn (t • x) = t • dawn x := by
  ext1 i
  apply Mink.ext_by <;> simp [dawn, place]

variable {G : Gauge} {L : Register G} {S : Table L} (F : Waves S) (W : Surface S)

private lemma patch (hF : F.Breathes) (hp : F.during W)
    (v : Fin n → S.Union) {y : Heights n} (hy : y ∈ sunrise n) :
    IsVanishingOn (Distn.fourier (W.W n v)) {x : Points n | inner ℝ (dawn y) x < -1} := by
  rw [Distn.from_compact]; intro f hs hf
  let Y (t : ℝ) := t • y + (1 : ℝ) • rate n
  let z := (1 : ℝ) • rate n
  let l (t : ℝ) := lifts (dawn (Y t)) f hf
  have hu : Tendsto l atTop (𝓝 0) := by
    let g := lifts (dawn z) f hf
    have hg : HasCompactSupport ⇑g := remains ..
    have hx (x) (H : x ∈ tsupport g) : inner ℝ (dawn y) x ≤ -1 :=
      le_of_lt (hs (support_lifts (dawn z) f hf H))
    refine (lift_falls (dawn y) g hg hx).congr fun t => ?_
    ext1 x
    change lifts (t • dawn y) g hg x = lifts (dawn (t • y + z)) f hf x
    rw [dawn_add, dawn_smul]
    simp only [g, rises, inner_add_left, Complex.ofReal_add, Complex.exp_add, mul_assoc]
  obtain ⟨m, C, -, H⟩ := hF n v
  have hw : Tendsto (fun t => weight (Probe.hat (l t))) atTop (𝓝 0) := by
    let A : Joint n →L[ℂ] Joint n := Probe.hat
    have hv := (((weight_cont (n := n)).comp A.continuous).tendsto 0).comp hu
    simpa only [Function.comp_def, map_zero, feath] using hv
  have hle : ‖Distn.fourier (W.W n v) f‖ ≤ C * (0 : ℝ) := by
    apply ge_of_tendsto (hw.const_mul C)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have he := sunrise_smul hy ht
    have hy' : Y t ∈ east n := dawns he zero_lt_one
    rw [hp n v (Y t) hy' f hf]
    have h1 : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
    have h := F.beam m C H he (Probe.hat (l t)) h1
    simp only [one_pow, one_mul] at h
    exact h
  rw [mul_zero] at hle
  exact norm_le_zero_iff.mp hle

theorem answer : YM.Bid.C06 := by
  -- `Region` and `Bounds` need not be invoked explicitly: `during` already gives the identity,
  -- and `beam` from the library can estimate the pairing with just the power bound. (`Bounds` in
  -- our hypotheses does ensure that the integrals used here, at strict heights, are genuine.)
  intro G L S T F W _ hF _ hp n v p hs
  apply mem_iInter.mpr
  rintro ⟨y, hy⟩
  change 0 ≤ inner ℝ (dawn y) p
  by_contra! hx
  let t := 2 / (-inner ℝ (dawn y) p)
  have ht : 0 < t := div_pos (by norm_num) (neg_pos.mpr hx)
  let s := {x : Points n | inner ℝ (dawn (t • y)) x < -1}
  have hh : IsOpen s := isOpen_lt (by fun_prop) continuous_const
  apply Set.disjoint_left.mp ((Distn.general_open _ hh).mp
    (patch F W hF hp v (sunrise_smul hy ht.le))) _ hs
  change inner ℝ (dawn (t • y)) p < -1
  rw [dawn_smul, real_inner_smul_left]
  have he : t * inner ℝ (dawn y) p = -2 := by
    dsimp only [t]
    field_simp [hx.ne]
  rw [he]
  norm_num

end YM.Work.C06
