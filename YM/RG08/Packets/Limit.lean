import YM.RG08.Packets.Norm

/-!
# Existence and quantitative cutoff stability in rooted norm
-/
noncomputable section
namespace YM.RG08.Packets
open Filter Finset Pert.Bulk
open scoped Topology ENNReal

set_option autoImplicit false
universe v w u
variable {J : Type v} {X : J → Type w} {Y : Type u} [NormedAddCommGroup Y]
    {e : Expense X} {K : ℕ → Sheet X Y} {T : Sheet X Y}

theorem ticket_of_limit {p : ℝ} (h : ∀ j x, Tendsto (fun n=> K n j x) atTop (𝓝 (T j x))) (hp : ∀ᶠ n in atTop, Ticket e (K n) p) : Ticket e T p := by
  intro j
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  let L (U : Sheet X Y) := ∑ x ∈ s, stamp (U j x) (e j x)
  have ht : Tendsto (fun n => L (K n)) atTop (𝓝 (L T)) := by
    apply tendsto_finsetSum
    intro i _
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((h j i).norm.mul_const _)
  exact le_of_tendsto ht (hp.mono fun n he=> (ENNReal.sum_le_tsum s).trans (he j))

variable [CompleteSpace Y]

/-- The rate need not be summable, the input comparisons are between arbitrary cutoffs.
Expense is *the same* at this fixed reporting level on both histories. -/
theorem stable {bill : ℕ→ℝ} (M : ℕ) (he : ∀ j x, 0 ≤ e j x) (hbill : Tendsto bill atTop (𝓝 0))
    (hp : ∀ i j, M ≤ i → i ≤ j → Ticket e (fun a x=> K i a x - K j a x) (bill i))
    (hB : ∀ i, M ≤ i → 0 ≤ bill i) :
    ∃ T : Sheet X Y,
      (∀ j x, Tendsto (fun n=> K n j x) atTop (𝓝 (T j x))) ∧
      ∀ i, M ≤ i → Ticket e (fun j x=> K i j x-T j x) (bill i) := by
  have ht (a : J) (x : X a) : ∃ t, Tendsto (fun i=> K (i+M) a x) atTop (𝓝 t) := by
    apply cauchySeq_tendsto_of_complete
    apply cauchySeq_of_le_tendsto_0' (fun i=>bill (i+M))
    · intro i j hj
      rw [dist_eq_norm]; exact (hp _ _ (by omega) (by omega)).below (hB _ (by omega)) he _ _
    exact (tendsto_add_atTop_iff_nat _).2 hbill
  choose T hT using ht
  have hf (a : J) (x : X a) : Tendsto (fun i=> K i a x) atTop (𝓝 (T a x)) :=
    (tendsto_add_atTop_iff_nat M).1 (hT a x)
  refine ⟨T,hf,fun i hi=> ?_⟩
  apply ticket_of_limit (K:=fun n a x=> K i a x-K n a x)
  · exact fun a x=> tendsto_const_nhds.sub (hf a x)
  exact (eventually_ge_atTop i).mono fun n hn=> hp _ _ hi hn

theorem solvent {bill : ℕ→ℝ} (M : ℕ) (he : ∀ j x, 0 ≤ e j x) (hbill : Tendsto bill atTop (𝓝 0))
    (hp : ∀ i j, M ≤ i → i ≤ j → Ticket e (fun a x=> K i a x - K j a x) (bill i))
    (hB : ∀ i, M ≤ i → 0 ≤ bill i) (p : ℝ) (hg : ∀ᶠ n in atTop, Ticket e (K n) p) :
    ∃ T : Sheet X Y,
      (∀ j x, Tendsto (fun n=> K n j x) atTop (𝓝 (T j x))) ∧
      (∀ i, M ≤ i → Ticket e (fun j x=> K i j x-T j x) (bill i)) ∧ Ticket e T p := by
  obtain ⟨T,hT,h⟩:=stable M he hbill hp hB; exact ⟨T,hT,h,ticket_of_limit hT hg⟩

 omit [CompleteSpace Y] in
/-- Kernel uniqueness is not modulo redistribution of stubs. Use after alignment. -/
theorem identical {U : Sheet X Y} {p q : ℕ→ℝ} {M : ℕ} (he : ∀ j x, 0 ≤ e j x) (hp : Tendsto p atTop (𝓝 0)) (hq : Tendsto q atTop (𝓝 0))
    (ht : ∀ i, M ≤ i → 0 ≤ p i ∧ Ticket e (fun a x=> K i a x - T a x) (p i))
    (hu : ∀ i, M ≤ i → 0 ≤ q i ∧ Ticket e (fun a x=> K i a x - U a x) (q i)) : T = U := by
  funext a x
  have hT (V : Sheet X Y) (q : ℕ→ℝ) (h : ∀ i,M ≤ i → 0 ≤ q i ∧ Ticket e (fun a x=>K i a x-V a x) (q i)) (hq : Tendsto q atTop (𝓝 0)) : Tendsto (fun i=> K i a x) atTop (𝓝 (V a x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ hq
    exact (eventually_ge_atTop M).mono fun i hi=> (h i hi).2.below (h i hi).1 he _ _
  exact tendsto_nhds_unique (hT _ _ ht hp) (hT _ _ hu hq)
end YM.RG08.Packets
