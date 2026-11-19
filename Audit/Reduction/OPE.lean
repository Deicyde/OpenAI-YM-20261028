import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

section OPEHelpers

/- `Hierarchy.grouped` is elaborated under `open scoped Classical` (its `Fintype.equivFin`
needs `DecidableEq`); we open it too so that our restatement below uses the same instances. -/
open scoped Classical

/-! ### Bookkeeping for `allZero` -/

/-- `allZero` is invariant under reindexing by an equivalence. -/
private theorem ope_allZero_comp_equiv {F : ℕ → Type} [∀ d, Zero (F d)] {ι κ : Type}
    (w : ι → Σ d, F d) (e : κ ≃ ι) : allZero (w ∘ e) = allZero w := by
  unfold allZero
  by_cases h : ∀ i, w i = zeroTag F
  · rw [if_pos h]
    exact if_pos (fun k => h (e k))
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    intro i
    simpa using h' (e.symm i)

/-- `allZero` of a concatenated word is the product. -/
private theorem ope_allZero_sumElim {F : ℕ → Type} [∀ d, Zero (F d)] {I J : Type}
    (a : I → Σ d, F d) (b : J → Σ d, F d) :
    allZero (Sum.elim a b) = allZero a * allZero b := by
  unfold allZero
  by_cases ha : ∀ i, a i = zeroTag F
  · by_cases hb : ∀ j, b j = zeroTag F
    · have hab : ∀ k, Sum.elim a b k = zeroTag F := fun k => by
        cases k with
        | inl i => exact ha i
        | inr j => exact hb j
      rw [if_pos ha, if_pos hb, if_pos hab, mul_one]
    · have hab : ¬ ∀ k, Sum.elim a b k = zeroTag F := fun h => hb fun j => h (Sum.inr j)
      rw [if_neg hb, if_neg hab, mul_zero]
  · have hab : ¬ ∀ k, Sum.elim a b k = zeroTag F := fun h => ha fun i => h (Sum.inl i)
    rw [if_neg ha, if_neg hab, zero_mul]

private theorem ope_allZero_unit_of_eq {F : ℕ → Type} [∀ d, Zero (F d)] {t : Σ d, F d}
    (h : t = zeroTag F) : allZero (fun _ : Unit => t) = 1 := by
  unfold allZero
  exact if_pos fun _ => h

private theorem ope_allZero_unit_of_ne {F : ℕ → Type} [∀ d, Zero (F d)] {t : Σ d, F d}
    (h : ¬ t = zeroTag F) : allZero (fun _ : Unit => t) = 0 := by
  unfold allZero
  exact if_neg fun h' => h (h' ())

private theorem ope_norm_allZero_le {F : ℕ → Type} [∀ d, Zero (F d)] {ι : Type}
    (w : ι → Σ d, F d) : ‖allZero w‖ ≤ 1 := by
  unfold allZero
  split_ifs <;> simp

/-- The double sum `∑ ∑ c (2N - Z)` splits linearly. -/
private theorem ope_sum_sum_two_mul_sub {α : Type} [Fintype α] {β : α → Type}
    [∀ k, Fintype (β k)] (c N Z : (k : α) → β k → ℂ) :
    ∑ k, ∑ i, c k i * (2 * N k i - Z k i) =
      2 * ∑ k, ∑ i, c k i * N k i - ∑ k, ∑ i, c k i * Z k i := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)

private theorem ope_weight_nonneg {I : Type} [Fintype I] (a : I → T₀.Tag) :
    0 ≤ T₀.weight a :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-! ### Coefficients -/

private theorem ope_coeff_none_zero {I : Type} [Fintype I] (a : I → T₀.Tag)
    (x : I → Spacetime) (o : Spacetime) : redCoefficient T₀ a 0 none x o = allZero a := by
  simp only [redCoefficient, ↓reduceIte]

private theorem ope_coeff_none_ne {I : Type} [Fintype I] (a : I → T₀.Tag) {j : ℕ}
    (hj : j ≠ 0) (x : I → Spacetime) (o : Spacetime) : redCoefficient T₀ a j none x o = 0 :=
  if_neg hj

private theorem ope_coeff_some_of_eq {I : Type} [Fintype I] (a : I → T₀.Tag) {j : ℕ}
    {i : T₀.Channel j} (h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field)
    (x : I → Spacetime) (o : Spacetime) : redCoefficient T₀ a j (some i) x o = 0 :=
  if_pos h

private theorem ope_coeff_some_of_ne {I : Type} [Fintype I] (a : I → T₀.Tag) {j : ℕ}
    {i : T₀.Channel j} (h : ¬ (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field)
    (x : I → Spacetime) (o : Spacetime) :
    redCoefficient T₀ a j (some i) x o = T₀.coefficient a j i x o :=
  if_neg h

/-- The coefficient bound for the reduced channels. -/
private theorem ope_coeff_bound (hO : T₀.OperatorProductExpansion) {I : Type} [Fintype I]
    (a : I → T₀.Tag) (M η ε : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε) (j : ℕ)
    (i : Option (T₀.Channel j)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x o, Hierarchy.Within r M η x o →
      ‖redCoefficient T₀ a j i x o‖ ≤ r ^ ((j:ℝ) - T₀.weight a - ε) := by
  rcases i with _ | i
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with r hr x o _
    by_cases hj : j = 0
    · subst hj
      rw [ope_coeff_none_zero]
      refine (ope_norm_allZero_le a).trans
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr.1 hr.2.le ?_)
      have := ope_weight_nonneg T₀ a
      push_cast
      linarith
    · rw [ope_coeff_none_ne T₀ a hj, norm_zero]
      exact Real.rpow_nonneg hr.1.le _
  · filter_upwards [hO.coefficients a M η ε hM hη hε j i, self_mem_nhdsWithin]
      with r hr hr0
    intro x o hW
    by_cases h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field
    · rw [ope_coeff_some_of_eq T₀ a h, norm_zero]
      exact Real.rpow_nonneg (Set.mem_Ioi.mp hr0).le _
    · rw [ope_coeff_some_of_ne T₀ a h]
      exact hr x o hW

/-! ### Grouped correlations of the reduced hierarchy, written with `T₀`'s data -/

/-- `redCorrelation` on the grouped configuration of `(a, x)` and `(b, y)`; this is
definitionally `(reduced T₀ μ hH).grouped s a x b y`. -/
private def opeGrouped (s : Option Phase) {I J : Type} [Fintype I] [Fintype J]
    (a : I → T₀.Tag) (x : I → Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) : ℂ :=
  redCorrelation T₀ s (Sum.elim a b ∘ (Fintype.equivFin (I ⊕ J)).symm)
    (WithLp.toLp 2 (Sum.elim x y ∘ (Fintype.equivFin (I ⊕ J)).symm))

/-- The OPE remainder of the reduced hierarchy at phase `s`, written with `T₀`'s data. -/
private def opeRem (s : Option Phase) {I J : Type} [Fintype I] [Fintype J]
    (a : I → T₀.Tag) (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) (D : ℕ) : ℂ :=
  opeGrouped T₀ s a x b y - ∑ j : Fin (D+1), ∑ i : Option (T₀.Channel j.val),
    redCoefficient T₀ a j.val i x o *
      opeGrouped T₀ s (fun _ : Unit => (⟨j.val, redActor T₀ j.val i⟩ : T₀.Tag)) (fun _ => o) b y

private theorem opeGrouped_none {I J : Type} [Fintype I] [Fintype J] (a : I → T₀.Tag)
    (x : I → Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) :
    opeGrouped T₀ none a x b y = allZero a * allZero b := by
  unfold opeGrouped
  simp only [redCorrelation]
  rw [ope_allZero_comp_equiv, ope_allZero_sumElim]

private theorem opeGrouped_phase0 {I J : Type} [Fintype I] [Fintype J] (a : I → T₀.Tag)
    (x : I → Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) :
    opeGrouped T₀ (some phase0) a x b y = T₀.grouped (some T₀.selected) a x b y := by
  unfold opeGrouped
  simp only [redCorrelation, ↓reduceIte]
  rfl

private theorem opeGrouped_other {p : Phase} (hp : p ≠ phase0) {I J : Type} [Fintype I]
    [Fintype J] (a : I → T₀.Tag) (x : I → Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) :
    opeGrouped T₀ (some p) a x b y =
      2 * opeGrouped T₀ none a x b y - opeGrouped T₀ (some phase0) a x b y := by
  unfold opeGrouped
  simp only [redCorrelation, if_neg hp, ↓reduceIte]

/-- A word containing the zero tag exists for any enumeration of `Unit ⊕ J`. -/
private theorem ope_exists_zero {J : Type} {n : ℕ} (σ : Fin n ≃ Unit ⊕ J) {t : T₀.Tag}
    (ht : t = zeroTag T₀.Field) (b : J → T₀.Tag) :
    ∃ i, (Sum.elim (fun _ : Unit => t) b ∘ σ) i = zeroTag T₀.Field :=
  ⟨σ.symm (Sum.inl ()), by simp [ht]⟩

/-- In `T₀`'s selected phase, a grouped word whose actor slot is the zero tag vanishes. -/
private theorem ope_grouped_unit_zero (hZ : ZeroInvisible T₀) {J : Type} [Fintype J]
    {t : T₀.Tag} (ht : t = zeroTag T₀.Field) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) :
    T₀.grouped (some T₀.selected) (fun _ : Unit => t) (fun _ => o) b y = 0 :=
  hZ _ _ _ (ope_exists_zero T₀ _ ht b)

/-! ### Inner sums over the channels `Option (T₀.Channel j)` -/

private theorem ope_inner_none {I : Type} [Fintype I] (a : I → T₀.Tag) (x : I → Spacetime)
    (o : Spacetime) (B : ℂ) (j : ℕ) :
    ∑ i : Option (T₀.Channel j), redCoefficient T₀ a j i x o *
        (allZero (fun _ : Unit => (⟨j, redActor T₀ j i⟩ : T₀.Tag)) * B) =
      if j = 0 then allZero a * B else 0 := by
  have hnone : redCoefficient T₀ a j none x o *
      (allZero (fun _ : Unit => (⟨j, redActor T₀ j none⟩ : T₀.Tag)) * B) =
      if j = 0 then allZero a * B else 0 := by
    by_cases hj : j = 0
    · subst hj
      rw [if_pos rfl, ope_coeff_none_zero,
        ope_allZero_unit_of_eq
          (show (⟨0, redActor T₀ 0 none⟩ : T₀.Tag) = zeroTag T₀.Field from rfl),
        one_mul]
    · rw [if_neg hj, ope_coeff_none_ne T₀ a hj, zero_mul]
  rw [Fintype.sum_option, hnone, Finset.sum_eq_zero, add_zero]
  intro i _
  by_cases h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field
  · rw [ope_coeff_some_of_eq T₀ a h, zero_mul]
  · rw [ope_allZero_unit_of_ne
      (show ¬ (⟨j, redActor T₀ j (some i)⟩ : T₀.Tag) = zeroTag T₀.Field from h),
      zero_mul, mul_zero]

private theorem ope_inner_phase0 (hZ : ZeroInvisible T₀) {I J : Type} [Fintype I]
    [Fintype J] (a : I → T₀.Tag) (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) (j : ℕ) :
    ∑ i : Option (T₀.Channel j), redCoefficient T₀ a j i x o *
        T₀.grouped (some T₀.selected) (fun _ : Unit => (⟨j, redActor T₀ j i⟩ : T₀.Tag))
          (fun _ => o) b y =
      ∑ i : T₀.Channel j, T₀.coefficient a j i x o *
        T₀.grouped (some T₀.selected) (fun _ : Unit => (⟨j, T₀.actor j i⟩ : T₀.Tag))
          (fun _ => o) b y := by
  have hnone : redCoefficient T₀ a j none x o *
      T₀.grouped (some T₀.selected) (fun _ : Unit => (⟨j, redActor T₀ j none⟩ : T₀.Tag))
        (fun _ => o) b y = 0 := by
    by_cases hj : j = 0
    · subst hj
      rw [ope_grouped_unit_zero T₀ hZ
        (show (⟨0, redActor T₀ 0 none⟩ : T₀.Tag) = zeroTag T₀.Field from rfl), mul_zero]
    · rw [ope_coeff_none_ne T₀ a hj, zero_mul]
  rw [Fintype.sum_option, hnone, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field
  · rw [ope_coeff_some_of_eq T₀ a h, zero_mul, ope_grouped_unit_zero T₀ hZ h, mul_zero]
  · rw [ope_coeff_some_of_ne T₀ a h]
    rfl

/-! ### The three phases -/

private theorem opeRem_none {I J : Type} [Fintype I] [Fintype J] (a : I → T₀.Tag)
    (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) (D : ℕ) :
    opeRem T₀ none a x o b y D = 0 := by
  unfold opeRem
  simp only [opeGrouped_none, ope_inner_none]
  rw [Fin.sum_univ_succ]
  simp

private theorem opeRem_phase0 (hZ : ZeroInvisible T₀) {I J : Type} [Fintype I] [Fintype J]
    (a : I → T₀.Tag) (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) (D : ℕ) :
    opeRem T₀ (some phase0) a x o b y D =
      T₀.grouped (some T₀.selected) a x b y - ∑ j : Fin (D+1), ∑ i : T₀.Channel j.val,
        T₀.coefficient a j.val i x o *
          T₀.grouped (some T₀.selected) (fun _ : Unit => ⟨j.val, T₀.actor j.val i⟩)
            (fun _ => o) b y := by
  unfold opeRem
  simp only [opeGrouped_phase0, ope_inner_phase0 T₀ hZ]

private theorem opeRem_other {p : Phase} (hp : p ≠ phase0) {I J : Type} [Fintype I]
    [Fintype J] (a : I → T₀.Tag) (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) (D : ℕ) :
    opeRem T₀ (some p) a x o b y D =
      2 * opeRem T₀ none a x o b y D - opeRem T₀ (some phase0) a x o b y D := by
  unfold opeRem
  simp only [opeGrouped_other T₀ hp]
  rw [ope_sum_sum_two_mul_sub]
  ring

/-- Every phase of the reduced remainder is bounded by `T₀`'s selected-phase remainder. -/
private theorem opeRem_bound (hZ : ZeroInvisible T₀) {I J : Type} [Fintype I] [Fintype J]
    (a : I → T₀.Tag) (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) (D : ℕ) (s : Option Phase) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ‖T₀.grouped (some T₀.selected) a x b y - ∑ j : Fin (D+1), ∑ i : T₀.Channel j.val,
        T₀.coefficient a j.val i x o *
          T₀.grouped (some T₀.selected) (fun _ : Unit => ⟨j.val, T₀.actor j.val i⟩)
            (fun _ => o) b y‖ ≤ B) :
    ‖opeRem T₀ s a x o b y D‖ ≤ B := by
  rcases s with _ | p
  · rw [opeRem_none, norm_zero]
    exact hB0
  · by_cases hp : p = phase0
    · subst hp
      rw [opeRem_phase0 T₀ hZ]
      exact hB
    · rw [opeRem_other T₀ hp, opeRem_none, opeRem_phase0 T₀ hZ, mul_zero, zero_sub, norm_neg]
      exact hB

end OPEHelpers

/-- The reduced hierarchy has an all-orders OPE with shared coefficients in every phase. -/
theorem reduced_ope {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure)
    (hO : T₀.OperatorProductExpansion) (hZ : ZeroInvisible T₀) :
    (reduced T₀ μ hH).OperatorProductExpansion := by
  refine ⟨?_, ?_⟩
  · intro I _ a M η ε hM hη hε j i
    exact ope_coeff_bound T₀ hO a M η ε hM hη hε j i
  · intro I J _ _ a b M η c ε hM hη hc hε D
    filter_upwards [hO.remainder a b M η c ε hM hη hc hε D, self_mem_nhdsWithin]
      with r hr hr0
    intro x o y hW hC s
    exact opeRem_bound T₀ hZ a x o b y D s (Real.rpow_nonneg (Set.mem_Ioi.mp hr0).le _)
      (hr x o y hW hC (some T₀.selected))

end YMAudit
