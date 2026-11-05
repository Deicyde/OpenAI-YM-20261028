import YM.Bid.Kitchen
set_option autoImplicit false
noncomputable section
namespace YM.Work.H01
open Filter Function Set RG Wilson Lattice Supply Pressure Shoot Ovens Ovens.Pipes
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators NNReal ENNReal ComplexOrder Classical

variable {G : Gauge} {n : Side}

-- The uncollected term at one alphabet subset. Right indices are Mayer
-- factors (`exp log - 1`), so there are no repeated addresses.
private def expanded (X : Pipes G n) (d : Tap G n) (P : BudgetPoint) (V : Config G n)
    (s : Finset Ovens.Label) : ℝ :=
  (X.pours d).gasOccurrence P (lefts s) V * ∏ i ∈ rights s, reach d (Sum.inr i) V

private lemma occ_admissible {A : Activities G n} {P : BudgetPoint} {b : Finset ℕ}
    {V : Config G n} (h : A.gasOccurrence P b V ≠ 0) : A.admissible P V b := by
  by_contra hh
  simp [Activities.gasOccurrence, hh] at h

private lemma expanded_of_admissible {X : Pipes G n} {d : Tap G n} {P : BudgetPoint}
    {V : Config G n} {s : Finset Ovens.Label} (h : (X.pours d).admissible P V (lefts s)) :
    expanded X d P V s = ∏ i ∈ s, reach d i V := by
  rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  unfold expanded Activities.gasOccurrence
  rw [if_pos h]
  rfl

-- Compulsory exact coverage and separation give the local flag equality.
private lemma intersection_of_admissible {A : Activities G n} {P : BudgetPoint}
    {V : Config G n} {b : Finset ℕ} (h : A.admissible P V b) {i : ℕ} (hi : i ∈ b) :
    (A.forced i).support ∩ flags P.threshold V = (A.forced i).inventory := by
  rw [← h.2]
  ext x
  rw [Finset.mem_inter]
  constructor
  · rintro ⟨hx, hU⟩
    obtain ⟨j, hj, hx'⟩ := Finset.mem_biUnion.mp hU
    by_cases hh : i = j
    · simpa [hh] using hx'
    exact False.elim <| Finset.disjoint_left.mp (h.1 hi hj hh) hx ((A.forced j).inventory_sup hx')
  · intro hx
    exact ⟨(A.forced i).inventory_sup hx, Finset.mem_biUnion.mpr ⟨i, hi, hx⟩⟩

section Collect
variable {X : Pipes G n} {d : Tap G n} {P : BudgetPoint} {V : Config G n}

private def flatten (F : ℕ ≃ Pellet X) (b : Finset ℕ) : Finset Ovens.Label :=
  b.biUnion fun i => (F i).val

private lemma val_injective (F : ℕ ≃ Pellet X) : Injective (fun i => (F i).val) :=
  fun _ _ h => F.injective (Subtype.ext h)

private lemma plot_flatten (F : ℕ ≃ Pellet X) (b : Finset ℕ) :
    X.plot (flatten F b) = b.biUnion fun i => X.plot (F i).val := by
  ext x
  simp only [plot, flatten, Finset.mem_biUnion, lefts, Finset.mem_toLeft]
  constructor
  · rintro ⟨j, ⟨i, hi, hj⟩, hx⟩
    exact ⟨i, hi, j, hj, hx⟩
  · rintro ⟨i, hi, j, hj, hx⟩
    exact ⟨j, ⟨i, hi, hj⟩, hx⟩

private lemma flatten_image (F : ℕ ≃ Pellet X) (b : Finset ℕ) :
    flatten F b = (b.image fun i => (F i).val).biUnion id := by
  ext
  simp [flatten]

private lemma patch_nonempty (X : Pipes G n) (j : Ovens.Label) : (X.patch j).Nonempty := by
  rcases j with j|j
  · exact (X.kernel j).inventory_ne.mono (X.kernel j).inventory_sup
  · exact X.sites j

variable {F : ℕ ≃ Pellet X} {b : Finset ℕ}

private lemma flatten_admissible (h : (fused F P d).admissible P V b) :
    (X.pours d).admissible P V (lefts (flatten F b)) := by
  constructor
  · intro i hi j hj hij
    obtain ⟨k, hk, hi'⟩ := Finset.mem_biUnion.mp (Finset.mem_toLeft.mp hi)
    obtain ⟨l, hl, hj'⟩ := Finset.mem_biUnion.mp (Finset.mem_toLeft.mp hj)
    by_cases hh : k = l
    · subst l
      have hpair := (F k).property.2.2
      exact hpair (Finset.mem_toLeft.mpr hi') (Finset.mem_toLeft.mpr hj') hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have ht : Disjoint (X.skin (F k).val) (X.skin (F l).val) := h.1 hk hl hh
    apply Finset.disjoint_left.mp ht
    · exact Finset.mem_biUnion.mpr ⟨Sum.inl i, hi', hx⟩
    · exact Finset.mem_biUnion.mpr ⟨Sum.inl j, hj', hy⟩
  · change X.plot (flatten F b) = _
    rw [plot_flatten]; exact h.2

private lemma flat_match {δ u : ℝ} (H : X.Digests d P δ u)
    (h : (fused F P d).admissible P V b) :
    expanded X d P V (flatten F b) = (fused F P d).gasOccurrence P b V := by
  have hpair : (b : Set ℕ).PairwiseDisjoint (fun i => (F i).val) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨x, hx⟩ := patch_nonempty X a
    have hg : Disjoint (X.skin (F i).val) (X.skin (F j).val) := h.1 hi hj hij
    apply Finset.disjoint_left.mp hg
    · exact Finset.mem_biUnion.mpr ⟨a, ha, hx⟩
    · exact Finset.mem_biUnion.mpr ⟨a, hb, hx⟩
  rw [expanded_of_admissible (flatten_admissible h), flatten, Finset.prod_biUnion hpair,
      Activities.gasOccurrence, if_pos h]
  apply Finset.prod_congr rfl
  intro i hi
  change ∏ a ∈ (F i).val, reach d a V = solid F P d i V
  unfold solid
  split
  · rfl
  next he =>
    by_contra hn
    apply he
    refine ⟨intersection_of_admissible h hi, ?_⟩
    intro j hj
    exact H.stamp.forced.permit j V
      (Finset.prod_ne_zero_iff.mp hn (Sum.inl j) (Finset.mem_toLeft.mp hj))

private lemma parts_flatten (h : (fused F P d).admissible P V b) :
    Ac.Parts X.patch (flatten F b) = b.image (fun i => (F i).val) := by
  rw [flatten_image]
  apply Ac.separates
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact (F i).property.2.1
  · intro p hp q hq hpq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    exact h.1 hi hj (fun e => hpq (congrArg (fun x => (F x).val) e))

-- Nonzero expanded terms have no free components: each attachment
-- hits a flag, accounted for by an old forced address in this term.
private lemma unflatten {δ u : ℝ} (H : X.Digests d P δ u)
    (F : ℕ ≃ Pellet X) {s : Finset Ovens.Label} (hn : expanded X d P V s ≠ 0) :
    ∃ c, (fused F P d).admissible P V c ∧ flatten F c = s := by
  have ha : (X.pours d).admissible P V (lefts s) :=
    occ_admissible (left_ne_zero_of_mul hn)
  rw [expanded_of_admissible ha] at hn
  let T := Ac.Parts X.patch s
  have hT (p) (hp : p ∈ T) : X.contains p := by
    obtain ⟨hps, hsp⟩ := Ac.lives X.patch s hp
    refine ⟨?_, hsp, ?_⟩
    · obtain ⟨j, hj⟩ := hsp.1
      rcases j with i | i
      · exact ⟨i, Finset.mem_toLeft.mpr hj⟩
      have he := Finset.prod_ne_zero_iff.mp hn _ (hps hj)
      have hh : ¬ Healthy P.threshold (X.softer i) V := by
        refine H.visits i V (fun e => he ?_)
        simp [reach, e]
      obtain ⟨x, hx, hx'⟩ := Finset.not_disjoint_iff.mp hh
      rw [← ha.2] at hx'
      obtain ⟨k, hk, hk'⟩ := Finset.mem_biUnion.mp hx'
      have hl := Finset.mem_toLeft.mp hk
      have hchain : Ac.chain X.patch s (Sum.inr i) (Sum.inl k) :=
        .single ⟨hps hj, hl, x, hx, (X.kernel k).inventory_sup hk'⟩
      refine ⟨k, Finset.mem_toLeft.mpr ?_⟩
      rw [← Ac.contains X.patch hp _ hj]
      exact (Ac.bright X.patch _ _).mpr ⟨hl, hchain⟩
    · intro i hi j hj hij
      exact ha.1 (Finset.toLeft_subset_toLeft hps hi) (Finset.toLeft_subset_toLeft hps hj) hij
  let chooseIndex := fun p : {p // p ∈ T} => F.symm ⟨p.val, hT p.val p.property⟩
  let c := T.attach.image chooseIndex
  have him : c.image (fun i => (F i).val) = T := by
    ext p
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hi
      simpa only [chooseIndex, Equiv.apply_symm_apply] using q.property
    · intro hp
      refine ⟨chooseIndex ⟨p, hp⟩, Finset.mem_image.mpr ?_, ?_⟩
      · exact ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩
      · simp [chooseIndex]
  have hc : flatten F c = s := by rw [flatten_image, him]; exact Ac.reconstruct X.patch s
  refine ⟨c, ⟨?_, ?_⟩, hc⟩
  · intro i hi j hj hij
    have hmem (l) (hl : l ∈ c) : (F l).val ∈ T := by
      rw [← him]; exact Finset.mem_image_of_mem _ hl
    exact Ac.separate X.patch s (hmem i hi) (hmem j hj) (fun e => hij (val_injective F e))
  · change c.biUnion (fun i => X.plot (F i).val) = _
    rw [← plot_flatten, hc]; exact ha.2

private lemma fused_hasSum_iff {δ u a : ℝ} (H : X.Digests d P δ u) :
    HasSum (fun b => (fused F P d).gasOccurrence P b V) a ↔
      HasSum (expanded X d P V) a := by
  let f := fun b => (fused F P d).gasOccurrence P b V
  let g := expanded X d P V
  have he (x : support f) : g (flatten F x.val) = f x.val :=
    flat_match H (occ_admissible x.property)
  let M : support f → support g := fun x => ⟨flatten F x.val, show g _ ≠ 0 by
    rw [he]; exact x.property⟩
  have hi : Injective M := by
    intro x y h
    have hw : flatten F x.val = flatten F y.val := congrArg Subtype.val h
    have hx : (fused F P d).admissible P V x.val := occ_admissible x.property
    have hy : (fused F P d).admissible P V y.val := occ_admissible y.property
    apply Subtype.ext
    apply Finset.image_injective (val_injective F)
    rw [← parts_flatten hx, ← parts_flatten hy, hw]
  have hs : Surjective M := by
    intro y
    obtain ⟨b, hb, heq⟩ := unflatten H F y.property
    have hn : b ∈ support f := by
      change (fused F P d).gasOccurrence P b V ≠ 0
      rw [← flat_match H hb, heq]; exact y.property
    exact ⟨⟨b, hn⟩, Subtype.ext heq⟩
  exact (Equiv.ofBijective M ⟨hi, hs⟩).hasSum_iff_of_support he
end Collect

private lemma mayer_sum (f : Finset ℕ → ℝ) (l : ℕ → ℝ)
    (hf : Summable (fun i => ‖f i‖)) (hl : Summable l) :
    HasSum (fun c : Finset (ℕ ⊕ ℕ) => f c.toLeft * (∏ i ∈ c.toRight, (Real.exp (l i) - 1)))
      ((∑' b, f b) * Real.exp (∑' i, l i)) := by
  let y := fun i => Real.exp (l i) - 1
  let g := fun b : Finset ℕ => ∏ i ∈ b, y i
  have hy : Summable y := by
    refine (hl.norm.mul_left 2).of_norm_bounded_eventually ?_
    filter_upwards [hl.norm.tendsto_cofinite_zero.eventually_le_const zero_lt_one] with i hi
    change ‖Real.exp (l i) - 1‖ ≤ 2 * ‖l i‖
    simp only [Real.norm_eq_abs] at hi ⊢
    exact Real.abs_exp_sub_one_le hi
  have hg : Summable g := summable_finsetProd_of_summable_norm hy.norm
  have hlog : Real.exp (∑' i, l i) = ∑' b, g b := by
    have hy' : (Real.exp ∘ l) = (fun i => 1 + y i) := by
      ext i
      change Real.exp (l i) = 1 + (Real.exp (l i) - 1)
      ring
    calc
      _ = ∏' i, (Real.exp ∘ l) i := hl.hasSum.rexp.tprod_eq.symm
      _ = ∏' i, (1 + y i) := by rw [hy']
      _ = _ := tprod_one_add hg
  let e : Finset Ovens.Label ≃ Finset ℕ × Finset ℕ := Finset.sumEquiv.toEquiv
  let p := fun b : Finset ℕ × Finset ℕ => f b.1 * g b.2
  have hp : HasSum p ((∑' b, f b) * Real.exp (∑' i, l i)) := by
    rw [hlog, tsum_mul_tsum_of_summable_norm hf hg.norm]
    exact (summable_mul_of_summable_norm hf hg.norm).hasSum
  have hz := (e.hasSum_iff (f := p)).mpr hp
  exact hz

/-- Collect on the actual series, not postulating summability of the new gas. -/
theorem gathered {X : Pipes G n} {d : Tap G n} {F : ℕ ≃ Pellet X} {δ u : ℝ} {P : BudgetPoint}
    (H : X.Digests d P δ u) (V : Config G n) :
    HasSum (fun b => (fused F P d).gasOccurrence P b V)
      ((X.pours d).gas P V * Real.exp (∑' i, d.logarithm i V)) := by
  apply (fused_hasSum_iff H).2
  exact mayer_sum (fun b => (X.pours d).gasOccurrence P b V) _
    ((Activities.gasSeries H.stamp).absolute V) (H.pays.summable V)

theorem answer : YM.Bid.H01 := by
  intro G n X d F δ u κ γ P H _ V
  exact (gathered (F := F) H V).tsum_eq

-- Independent check on the scope / empty-product corner (here does
-- not even need any bounds).
example (X : Pipes G n) (P : BudgetPoint) (F : ℕ ≃ Pellet X)
    (d : Tap G n) (V : Config G n) (h : flags P.threshold V = ∅)
    (hh : ∀ i, d.logarithm i V ≠ 0 → ¬Healthy P.threshold (X.softer i) V) :
    (fused F P d).gas P V = (X.pours d).gas P V * Real.exp (∑' i, d.logarithm i V) := by
  have he i : d.logarithm i V = 0 := by
    by_contra hn
    exact hh i hn (by simp [Healthy, h])
  rw [Activities.gas_one _ _ h, Activities.gas_one _ _ h]
  simp [he]
end YM.Work.H01
