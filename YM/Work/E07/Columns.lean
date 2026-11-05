import YM.Bid.Energy

/-!
# Absolute summation tools for E07

The basic estimate uses a *per-row* small amount and a globally summable
(here finite torus, but uniformly priced) excess. Thus it can propagate a
bound on only the nonzero inputs of the rows being tested. With `unzip`, use
the column bound for the uniform small piece, and the **row** bound of the
original Pay matrix for the excess. Include the actual Bool slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.E07
open Function Lattice RG Finset Wilson Pressure Pressure.Stores Bid
open scoped InnerProductSpace BigOperators

variable {G : Gauge} {m n : Side}

section finite
variable {α β : Type*} [Fintype α]

/-- Bound the small part by a row sum. The inputs outside the nonzero
stencil need no bound. -/
lemma small_sum {k : α → ℝ} (hk : ∀ i, 0 ≤ k i) {r u : ℝ} (hr : ∑ i, k i ≤ r)
    (hu : 0 ≤ u) {g h : α → ℝ} (hh : ∀ i, 0 < k i → g i ≤ u + h i) :
    ∑ i, k i * g i ≤ r * u + ∑ i, k i * h i := by
  calc
    _ ≤ ∑ i, k i * (u + h i) := sum_le_sum fun i _ => by
      rcases eq_or_lt_of_le (hk i) with e|e
      · rw [← e, zero_mul, zero_mul]
      exact mul_le_mul_of_nonneg_left (hh i e) e.le
    _ = (∑ i, k i) * u + ∑ i, k i * h i := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ _ := by gcongr

variable [Fintype β]

/-- Bound the total excess charged by a set of rows, using full columns. -/
lemma excess_sum (k : α → β → ℝ) (s : Finset α) (hk : ∀ i j, 0 ≤ k i j)
    {b : ℝ} (hc : ∀ j, ∑ i, k i j ≤ b) {g : β → ℝ} (hg : ∀ j, 0 ≤ g j) :
    ∑ i ∈ s, ∑ j, k i j * g j ≤ b * ∑ j, g j := by
  rw [sum_comm, Finset.mul_sum]; apply sum_le_sum
  intro j _
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right ?_ (hg j)
  exact (sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun i _ _ => hk i j)).trans (hc j)

variable (F : α → β → Pay G)

omit [Fintype β] in
lemma unzip_norm (v : α → G.Color) (j : β) : ‖unzip F v j‖ ≤ ∑ i, ‖F i j‖ * ‖v i‖ := by
  unfold unzip
  apply (norm_sum_le _ _).trans
  exact sum_le_sum fun i _ => by
    simpa only [LinearIsometryEquiv.norm_map] using ((ContinuousLinearMap.adjoint (F i j)).le_opNorm (v i))

lemma unzip_total (s : Finset β) (v : α → G.Color) {g : α → ℝ} (hg : ∀ i, 0 ≤ g i)
    {r c u : ℝ} (hr : ∀ i, ∑ j, ‖F i j‖ ≤ r) (hc : ∀ j, ∑ i, ‖F i j‖ ≤ c) (hu : 0 ≤ u)
    (hv : ∀ j ∈ s, ∀ i, F i j ≠ 0 → ‖v i‖ ≤ u + g i) :
    ∑ j ∈ s, ‖unzip F v j‖ ≤ (s.card : ℝ) * (c * u) + r * ∑ i, g i := by
  calc
    _ ≤ ∑ j ∈ s, (c * u + ∑ i, ‖F i j‖ * g i) := sum_le_sum fun j hj =>
      (unzip_norm F v j).trans (small_sum (fun _ => norm_nonneg _) (hc j) hu
        (fun i hi => hv j hj i (norm_pos_iff.mp hi)))
    _ = (s.card : ℝ) * (c * u) + ∑ j ∈ s, ∑ i, ‖F i j‖ * g i := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      gcongr; exact excess_sum (fun j i => ‖F i j‖) _ (fun _ _ => norm_nonneg _) hr hg

omit [Fintype β] in
lemma unzip_uniform (v : α → G.Color) {c u : ℝ} (j : β) (hc : ∑ i, ‖F i j‖ ≤ c) (hu : 0 ≤ u)
    (hv : ∀ i, ‖v i‖ ≤ u) : ‖unzip F v j‖ ≤ c * u := by
  refine (unzip_norm F v j).trans ?_
  calc
    _ ≤ ∑ i, ‖F i j‖ * u := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
    _ ≤ c * u := by rw [← Finset.sum_mul]; gcongr

omit [Fintype α] in
lemma zip_uniform (v : β → G.Color) {r u : ℝ} (i : α) (hr : ∑ j, ‖F i j‖ ≤ r) (hu : 0 ≤ u)
    (hv : ∀ j, ‖v j‖ ≤ u) : ‖zip F v i‖ ≤ r * u := by
  unfold zip
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j, ‖F i j‖ * u := sum_le_sum fun j _ => ((F i j).le_opNorm (v j)).trans
      (mul_le_mul_of_nonneg_left (hv j) (norm_nonneg _))
    _ ≤ _ := by rw [← Finset.sum_mul]; gcongr
end finite

section paths
variable {P : PathData G} {c : Clip} {x t D : ℝ} {d : ℕ} {f : Site n → Site m}
    (hp : LaneCounts P x t c D d f) {E : Cell n → ℝ}

/-- Majorizes the excess for either Bool slot at a face. -/
def plottedExcess (P : PathData G) (c : Clip) (x : ℝ) (d : ℕ) (E : Cell n → ℝ) (p : Cell n) : ℝ :=
    Real.sqrt c.direct * E p + ∑ i, crunch P (till x) d p i * E i

include hp
lemma plottedExcess_nonneg (hE : ∀ i, 0 ≤ E i) (p : Cell n) : 0 ≤ plottedExcess P c x d E p := by
  exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hE _))
    (sum_nonneg fun i _ => mul_nonneg (hp.attic _ i) (hE _))

lemma plottedExcess_total (hE : ∀ i, 0 ≤ E i) :
    ∑ p : Twin n, plottedExcess P c x d E p.1 ≤ 2 * (Real.sqrt c.direct + D) * ∑ i, E i := by
  have he : ∑ p : Cell n, plottedExcess P c x d E p ≤ (Real.sqrt c.direct + D) * ∑ i, E i := by
    unfold plottedExcess
    rw [sum_add_distrib, ← Finset.mul_sum, add_mul]; gcongr
    exact excess_sum _ univ hp.attic hp.back hE
  unfold Twin; rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
  rw [mul_assoc]; gcongr

lemma plotted_le (U : Config G n) (hE : ∀ i, 0 ≤ E i) (p : Twin n) (hD : 0 ≤ D)
    {u : ℝ} (hu : 0 ≤ u) (hh : ∀ z : Cell n, separation (f p.1.1) (f z.1) ≤ radiusB x / 50 → toll U z ≤ u + E z) :
    ‖plotted P c (till x) d U p‖ ≤ (Real.sqrt c.direct + D) * u + plottedExcess P c x d E p.1 := by
  unfold plotted plottedExcess
  split
  · have H := small_sum (hp.attic p.1) (hp.finite p.1) hu (fun i hi => hh i (hp.maps _ _ hi))
    apply ((hp.valued p.1 U).trans H).trans
    rw [add_mul]
    exact add_le_add (le_add_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) hu))
      (le_add_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) (hE _)))
  unfold shoot
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply le_trans (mul_le_mul_of_nonneg_left ((G.curvature_norm _).trans (hh p.1 (by simp))) (Real.sqrt_nonneg _))
  rw [mul_add, add_mul]
  exact add_le_add (le_add_of_nonneg_right (mul_nonneg hD hu))
    (le_add_of_nonneg_right (sum_nonneg fun i _ => mul_nonneg (hp.attic _ i) (hE _)))

/-- Use the local envelope for all tested rows, pay total excess only once. -/
lemma plotted_total (U : Config G n) (s : Finset (Twin n)) (hE : ∀ i, 0 ≤ E i)
    (hD : 0 ≤ D) {u : ℝ} (hu : 0 ≤ u)
    (hh : ∀ p ∈ s, ∀ z : Cell n, separation (f p.1.1) (f z.1) ≤ radiusB x / 50 → toll U z ≤ u + E z) :
    ∑ p ∈ s, ‖plotted P c (till x) d U p‖ ≤
      (s.card : ℝ) * ((Real.sqrt c.direct + D) * u) + 2 * (Real.sqrt c.direct + D) * ∑ i, E i := by
  refine (sum_le_sum (s := s) (fun p hi => plotted_le hp U hE p hD hu (hh p hi))).trans ?_
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  gcongr
  exact le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun _ _ _ => plottedExcess_nonneg hp hE _))
    (plottedExcess_total hp hE)
end paths

end YM.Work.E07
