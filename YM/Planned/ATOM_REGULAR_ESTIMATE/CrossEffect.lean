import YM.Analysis.Homogeneous


/-!
Arity prices for pulling ordered left-derivative estimates back to link-chart
polars; independent of the lattice side. Cross-effect form also for testing the
graded polynomial directions (vary a tensor in all the arguments, retain every
assignment covering them).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Tensor
open scoped BigOperators Topology

section
variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq ι] [Fintype ι] {k : ℕ}

lemma mobius_cover (b : Finset ι) :
    (∑ s : Finset ι with b ⊆ s, (-1 : ℝ)^sᶜ.card) = if b = Finset.univ then 1 else 0 := by
  have he : (∑ t ∈ (bᶜ).powerset, (-1 : ℝ)^t.card) = if b = Finset.univ then 1 else 0 := by
    have hx := Finset.sum_powerset_neg_one_pow_card (x:=bᶜ)
    by_cases h : b = Finset.univ
    · subst b
      simp
    · have hu : bᶜ ≠ ∅ := fun H => h (by simpa using congr_arg (fun x : Finset ι => xᶜ) H)
      rw [if_neg h]
      rw [if_neg hu] at hx
      exact_mod_cast hx
  refine Eq.trans (Finset.sum_bij' (fun s _ => sᶜ) (fun t (_ : t ∈ bᶜ.powerset) => tᶜ)
    ?_ ?_ (fun _ _ => compl_compl _) (fun _ _ => compl_compl _) (fun _ _ => rfl)) he
  · intro s hs
    exact Finset.mem_powerset.mpr (compl_le_compl (show b ≤ s from (Finset.mem_filter.mp hs).2))
  intro t ht
  have h := compl_le_compl (show t ≤ bᶜ from Finset.mem_powerset.mp ht)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using h⟩

lemma diagonal_subsum (A : T E F k) (v : ι → E) (s : Finset ι) :
    diagonal A (∑ i ∈ s, v i) = ∑ r : Fin k → ι, if Finset.univ.image r ⊆ s then A (v ∘ r) else 0 := by
  rw [diagonal, A.map_sum_finset (fun _ i => v i) (fun _ => s), ← Finset.sum_filter]
  congr 1
  ext; simp [Finset.subset_iff]

open scoped Classical in
lemma cross_effect (A : T E F k) (v : ι → E) :
    (∑ s : Finset ι, (-1 : ℝ)^sᶜ.card • diagonal A (∑ i ∈ s, v i)) =
      ∑ r : Fin k → ι with Surjective r, A (v ∘ r) := by
  simp_rw [diagonal_subsum, Finset.smul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hu : Finset.univ.image r = Finset.univ ↔ Surjective r := by
    simp [Finset.ext_iff,Surjective]
  have he (s : Finset ι) : (-1:ℝ)^sᶜ.card • (if Finset.univ.image r ⊆ s then A (v ∘ r) else 0) =
      if Finset.univ.image r ⊆ s then (-1:ℝ)^sᶜ.card • A (v ∘ r) else 0 := by split <;> simp [*]
  simp_rw [he,← Finset.sum_filter, ← Finset.sum_smul]
  by_cases h : Surjective r <;> simp [mobius_cover (Finset.univ.image r),hu,h]

open scoped Classical in
lemma perm_effect (A : T E F k) (h : Sym A) (v : Fin k → E) :
    (∑ f : Fin k → Fin k with Surjective f, A (v ∘ f)) =
      (((Finset.univ.filter (fun f : Fin k → Fin k => Surjective f)).card : ℝ) • A v) := by
  let S := Finset.univ.filter (fun f : Fin k → Fin k => Surjective f)
  change (∑ f∈S, A _) = (S.card:ℝ) • _
  rw [Nat.cast_smul_eq_nsmul,← Finset.sum_const]
  refine Finset.sum_congr rfl fun f hf => ?_
  have he : Surjective f := (Finset.mem_filter.mp hf).2
  exact h v (Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr he,he⟩)

open scoped Classical in
lemma perm_cost_pos (n : ℕ) : 0 < (Finset.univ.filter (fun f : Fin n → Fin n => Surjective f)).card :=
  Finset.card_pos.mpr ⟨id, Finset.mem_filter.mpr ⟨Finset.mem_univ _,surjective_id⟩⟩

/-- Arity-only conversion at any volume and even at degenerate color
or direction spaces. No estimates from the norm of a global `Smooth`
operator are needed. -/
def polarCost (k : ℕ) : ℝ := (2^k) * ((k+1:ℝ)^k)

lemma polar_one (k : ℕ) : 1 ≤ polarCost k :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)))

lemma polarizes {A : T E F k} (h : Sym A) {C : ℝ}
    (hc : ∀ x : E, ‖x‖ ≤ 1 → ‖diagonal A x‖ ≤ C) (w : Fin k → E) (hw : ∀ i, ‖w i‖ ≤ 1) :
    ‖A w‖ ≤ polarCost k * C := by
  classical
  have he := cross_effect A w
  rw [perm_effect A h] at he
  let m := ((Finset.univ.filter (fun f : Fin k → Fin k => Surjective f)).card : ℝ)
  let r : ℝ := k+1
  have hm : 1 ≤ m := by
    unfold m; exact_mod_cast (show 1 ≤ _ from Nat.succ_le_iff.mpr (perm_cost_pos k))
  have hr : 0 < r := by unfold r; positivity
  have hs (s : Finset (Fin k)) : ‖∑ i ∈ s, w i‖ ≤ r := calc
    _ ≤ ∑ i ∈ s, ‖w i‖ := norm_sum_le ..
    _ ≤ ∑ _i ∈ s, (1:ℝ) := Finset.sum_le_sum fun i _ => hw i
    _ ≤ k := by
      have ht : s.card ≤ k := (Finset.card_le_univ s).trans_eq (Fintype.card_fin _)
      simpa using (show (s.card:ℝ) ≤ k by exact_mod_cast ht)
    _ ≤ r := le_add_of_nonneg_right zero_le_one
  have hi (x : E) (hx : ‖x‖ ≤ r) : ‖diagonal A x‖ ≤ r^k * C := by
    let y := r⁻¹ • x
    have hxy : r • y = x := by unfold y; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
    have hy : ‖y‖ ≤ 1 := by
      rw [← hxy,norm_smul_of_nonneg hr.le] at hx
      exact le_of_mul_le_mul_left (hx.trans_eq (mul_one r).symm) hr
    rw [← hxy, homogeneous, norm_smul_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hc y hy) (by positivity)
  change (∑ _s : Finset (Fin k), _) = m • A w at he
  calc
    _ ≤ m*‖A w‖ := le_mul_of_one_le_left (norm_nonneg _) hm
    _ ≤ ∑ _s : Finset (Fin k), r^k*C := by
      rw [← norm_smul_of_nonneg (zero_le_one.trans hm), ← he]
      refine (norm_sum_le ..).trans (Finset.sum_le_sum fun s _ => ?_)
      rw [norm_smul,norm_pow]; simpa using hi _ (hs s)
    _ = polarCost k*C := by simp [polarCost,r,mul_assoc]

lemma op_le_of_unit {A : T E F k} {C : ℝ} (hp : 0 ≤ C)
    (hw : ∀ v : Fin k → E, (∀ i, ‖v i‖ ≤ 1) → ‖A v‖ ≤ C) : ‖A‖ ≤ C := by
  refine ContinuousMultilinearMap.opNorm_le_bound hp fun w => ?_
  let v : Fin k → E := fun i => ‖w i‖⁻¹ • w i
  have he i : ‖w i‖ • v i = w i := by
    by_cases ht : w i = 0
    · simp [ht]
    simp [v,smul_smul,(norm_pos_iff.mpr ht).ne']
  have h i : ‖v i‖ ≤ 1 := by
    by_cases ht : w i = 0
    · simp [v,ht]
    change ‖‖w i‖⁻¹ • w i‖ ≤ 1
    rw [norm_smul_of_nonneg (inv_pos.mpr (norm_pos_iff.mpr ht)).le, inv_mul_cancel₀ (norm_pos_iff.mpr ht).ne']
  have hnn : 0 ≤ ∏ i, ‖w i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  conv_lhs => rw [← funext he]
  rw [A.map_smul_univ _ v, norm_smul_of_nonneg hnn]
  exact (mul_le_mul_of_nonneg_left (hw v h) hnn).trans_eq (mul_comm ..)

lemma op_polar {A : T E F k} (h : Sym A) {C : ℝ} (hp : 0 ≤ C)
    (hc : ∀ x : E, ‖x‖ ≤ 1 → ‖diagonal A x‖ ≤ C) : ‖A‖ ≤ polarCost k * C :=
  op_le_of_unit (mul_nonneg (zero_le_one.trans (polar_one k)) hp) (polarizes h hc)

end -- cross effects
end YM.Planned.AtomRegular
