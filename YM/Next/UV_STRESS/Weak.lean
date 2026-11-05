import YM.Org.Input


/-!
# Local weak bounds and the through-ties step used for UV curves

For a scalar **kernel** (only tests on Conf), local uniform *order zero in
joint tests*. Constants can depend on both weights and arity when used below.
Not pixelwise convergence of cutoff fields, and not implied here just by
qualitative distribution convergence.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Measure Analysis
open scoped Topology ContDiff BigOperators
variable {n : ℕ}

/-- Local order-zero vanishing, with smoothness on Conf. Allows arbitrary
collision values and derivatives are never paid on collisions. Ordinary
complex linear integration; in particular this is a bound already including
coordinate-projection ties *within* Conf. -/
structure Fades (K : ℕ → Points n → ℂ) : Prop where
  smooth (k : ℕ) : ContDiffOn ℝ ∞ (K k) (conf n)
  reads (s : Set (Points n)) : IsCompact s → s ⊆ conf n → ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k : ℕ in atTop, ∀ t : Test n, tsupport t ⊆ s → (∀ x, ‖t x‖ ≤ M) → ‖t.applyTo (K k)‖ ≤ ε

lemma test_add (F H : Points n → ℂ) (hF : ContinuousOn F (conf n)) (hH : ContinuousOn H (conf n))
    (t : Test n) : t.applyTo (F+H)=t.applyTo F+t.applyTo H := by
  unfold Test.applyTo
  simp_rw [Pi.add_apply, mul_add]
  exact integral_add (t.smearing hF) (t.smearing hH)

lemma test_smul (F : Points n → ℂ) (c : ℂ) (t : Test n) : t.applyTo (c • F) = c * t.applyTo F := by
  unfold Test.applyTo
  rw [← integral_const_mul]
  congr! 2; rename_i x; change _ * (c * _) = _; ring

lemma test_sub (F H : Points n → ℂ) (hF : ContinuousOn F (conf n)) (hH : ContinuousOn H (conf n))
    (t : Test n) : t.applyTo (F-H)=t.applyTo F-t.applyTo H := by
  unfold Test.applyTo
  simp_rw [Pi.sub_apply,mul_sub]
  exact integral_sub (t.smearing hF) (t.smearing hH)

lemma test_bounded (t : Test n) : ∃ M : ℝ, 0 < M ∧ ∀ x, ‖t x‖ ≤ M := by
  obtain ⟨M,hM⟩ := ((show IsCompact (tsupport t) from t.hasCompactSupport).image
    t.continuous.norm).bddAbove
  refine ⟨max 1 M,zero_lt_one.trans_le (le_max_left ..),fun x => ?_⟩
  by_cases h : x ∈ tsupport t
  · exact le_trans (hM (mem_image_of_mem _ h)) (le_max_right ..)
  simp only [image_eq_zero_of_notMem_tsupport h, norm_zero]; exact zero_le_one.trans (le_max_left ..)

lemma bounded_apply {F : Points n → ℂ} (hF : ContinuousOn F (conf n)) (s : Set (Points n))
    (hs : IsCompact s) (hC : s ⊆ conf n) (M : ℝ) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : Test n, tsupport t ⊆ s → (∀ x, ‖t x‖ ≤ M) → ‖t.applyTo F‖ ≤ A := by
  classical
  obtain ⟨C,hB⟩ := (hs.image_of_continuousOn ((hF.mono hC).norm)).bddAbove
  let g := s.indicator fun _ => M * max C 0
  have hp : Integrable g := by
    apply integrable_indicator_iff hs.measurableSet |>.2
    exact integrableOn_const hs.measure_lt_top.ne
  refine ⟨∫ x, g x, integral_nonneg (Set.indicator_nonneg fun x _ => mul_nonneg hM (le_max_right ..)),?_⟩
  intro t ht H
  apply norm_integral_le_of_norm_le hp
  filter_upwards with x
  by_cases hx : x ∈ s
  · change ‖t x * F x‖ ≤ _
    rw [norm_mul, show g x = _ from indicator_of_mem hx _]; exact mul_le_mul (H x)
      (le_trans (hB (mem_image_of_mem _ hx)) (le_max_left ..)) (norm_nonneg _) hM
  have hv : x ∉ tsupport t := fun hh => hx (ht hh)
  change ‖t x * F x‖ ≤ _
  rw [image_eq_zero_of_notMem_tsupport hv,zero_mul,norm_zero,show g x=0 from indicator_of_notMem hx _]

namespace Fades
variable {K H : ℕ → Points n → ℂ}

lemma zero (n : ℕ) : Fades (0 : ℕ → Points n → ℂ) where
  smooth _ := contDiffOn_const
  reads _ _ _ _ _ ε he := Eventually.of_forall fun _ t _ _ => by simp [Test.applyTo, he.le]

lemma loc (h : Fades K) (k : ℕ) : Dash.Loc (K k) := fun f => f.smearing (h.smooth k).continuousOn

lemma at_test (h : Fades K) (t : Test n) : Tendsto (fun k => t.applyTo (K k)) atTop (𝓝 0) := by
  obtain ⟨M,hM,hv⟩ := test_bounded t
  refine Metric.tendsto_nhds.mpr (fun ε he => ?_)
  filter_upwards [h.reads _ t.hasCompactSupport t.tsupport_subset M hM _ (half_pos he)] with k hk
  simpa [dist_zero_right] using (hk _ (Subset.refl _) hv).trans_lt (half_lt_self he)

lemma congr (h : Fades K) (hs : ∀ k, ContDiffOn ℝ ∞ (H k) (conf n))
    (he : ∀ᶠ k in atTop, EqOn (K k) (H k) (conf _)) : Fades H where
  smooth := hs
  reads s hu hv M hM ε hε := by
    filter_upwards [h.reads s hu hv M hM ε hε, he] with k hk he t ht hi
    rw [← Test.apply_eq t he]; exact hk _ ht hi

lemma plus (h : Fades K) (p : Fades H) : Fades (K+H) where
  smooth k := (h.smooth k).add (p.smooth k)
  reads s hu hv M hM ε hε := by
    filter_upwards [h.reads s hu hv M hM _ (half_pos hε), p.reads s hu hv M hM _ (half_pos hε)] with k hk hp t hT hc
    rw [Pi.add_apply,test_add _ _ (h.smooth k).continuousOn (p.smooth k).continuousOn]
    exact le_trans (norm_add_le _ _) ((add_le_add (hk _ hT hc) (hp _ hT hc)).trans_eq (add_halves _))

lemma times (h : Fades K) {c : ℕ → ℂ} {d : ℂ} (hp : Tendsto c atTop (𝓝 d)) :
    Fades (fun k => c k • K k) where
  smooth k := contDiffOn_const.smul (h.smooth k)
  reads s hu hv M hM ε hε := by
    let A := ‖d‖ + 1
    have hA : 0 < A := by dsimp only [A]; positivity
    filter_upwards [h.reads s hu hv M hM _ (div_pos hε hA), hp.norm.eventually (ge_mem_nhds (show ‖d‖ < A by dsimp [A]; linarith))] with k hk he t ht hi
    rw [test_smul,norm_mul]
    exact (mul_le_mul he (hk _ ht hi) (norm_nonneg _) hA.le).trans_eq (mul_div_cancel₀ _ hA.ne')

lemma small_scalar {F : Points n → ℂ} (h : ContDiffOn ℝ ∞ F (conf n)) {c : ℕ → ℂ}
    (hc : Tendsto c atTop (𝓝 0)) : Fades (fun k => c k • F) where
  smooth k := contDiffOn_const.smul h
  reads s hu hv M hM ε hε := by
    obtain ⟨A,hA,hB⟩ := bounded_apply h.continuousOn s hu hv M hM.le
    have he : Tendsto (fun k => ‖c k‖*A) atTop (𝓝 0) := by simpa using hc.norm.mul_const A
    filter_upwards [he.eventually (ge_mem_nhds hε)] with k hk t ht hp
    rw [test_smul,norm_mul]
    exact (mul_le_mul_of_nonneg_left (hB _ ht hp) (norm_nonneg _)).trans hk

lemma sum {ι : Type*} (f : ι → ℕ → Points n → ℂ) (s : Finset ι) (h : ∀ i ∈ s, Fades (f i)) :
    Fades (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact zero n
  | @insert x s he ih =>
    rw [Finset.sum_insert he]; exact (h x (Finset.mem_insert_self ..)).plus
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end Fades
end YM.Next.UVStress
