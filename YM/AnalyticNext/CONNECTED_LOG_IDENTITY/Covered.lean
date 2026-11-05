import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Words
import YM.Push.ABSOLUTE_SUMS.Absence



set_option warningAsError false

/-!
# The *covered* gas at fixed V

Unforced activities indexed by ι, forced by κ. No claim that the log
of the COVERED sum (may even vanish) is given by the unforced cluster
coefficients. Rather, the clusters give the additive bulk exponent,
and incur a particular exponential charge against EACH family of
forced d addresses. Use this before merging those charges into the
format for the next RG step; as always use series under absolute checks.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity

open Lattice Wilson RG AbsoluteSums  Finset Filter Function Ursell
open scoped Classical BigOperators Topology

variable {ι κ : Type*} {n : Side}

def setSplit : Finset κ × Finset ι ≃ Finset (κ ⊕ ι) where
  toFun p := p.1.disjSum p.2
  invFun s := (s.toLeft,s.toRight)
  left_inv _ := Prod.ext toLeft_disjSum toRight_disjSum
  right_inv _ := toLeft_disjSum_toRight

/-- A forced plus unforced geometry. -/
abbrev both (Y : κ → Support n) (X : ι → Support n) := Sum.elim Y X
abbrev onlyL (I : κ → Support n) : κ ⊕ ι → Support n := Sum.elim I (fun _ => ∅)

lemma disj_union {ν : Type*} [DecidableEq ν] (A : Finset κ) (B : Finset ι) (Y : κ → Finset ν) (X : ι → Finset ν) :
    (A.disjSum B).biUnion (Sum.elim Y X) = A.biUnion Y ∪ B.biUnion X := by
  ext x
  simp only [mem_biUnion,mem_union]
  constructor
  · rintro ⟨i,h,hx⟩; cases i <;> first
      | exact Or.inl ⟨_,inl_mem_disjSum.mp h,hx⟩
      | exact Or.inr ⟨_,inr_mem_disjSum.mp h,hx⟩
  rintro (⟨i,h,hx⟩|⟨i,h,hx⟩)
  · exact ⟨Sum.inl i,inl_mem_disjSum.mpr h,hx⟩
  exact ⟨Sum.inr i,inr_mem_disjSum.mpr h,hx⟩

lemma apart_split (A : Finset κ) (B : Finset ι) (Y : κ → Support n) (X : ι → Support n) :
    Apart (both Y X) (A.disjSum B) ↔
    Apart Y A ∧ Apart X B ∧ (∀ j∈B, Disjoint (A.biUnion Y) (X j)) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro i hi j hj he
      change Disjoint (both Y X (Sum.inl i)) (both Y X (Sum.inl j))
      exact h (inl_mem_disjSum.mpr hi) (inl_mem_disjSum.mpr hj) (fun x => he (Sum.inl.inj x))
    · intro i hi j hj he
      change Disjoint (both Y X (Sum.inr i)) (both Y X (Sum.inr j))
      exact h (inr_mem_disjSum.mpr hi) (inr_mem_disjSum.mpr hj) (fun x => he (Sum.inr.inj x))
    intro j hj
    rw [disjoint_biUnion_left]; intro i hi
    change Disjoint (both Y X (Sum.inl i)) (both Y X (Sum.inr j))
    exact h (inl_mem_disjSum.mpr hi) (inr_mem_disjSum.mpr hj) (by simp)
  rintro ⟨h1,h2,h3⟩
  have he {i j} (hi : i ∈ A) (hj : j∈B) : Disjoint (Y i) (X j) :=
    (disjoint_biUnion_left ..).mp (h3 j hj) i hi
  intro i hi j hj hh
  cases i with
  | inl i =>
    have hi := inl_mem_disjSum.mp (show Sum.inl i ∈ A.disjSum B from hi)
    cases j with
    | inl j =>
      exact h1 hi (inl_mem_disjSum.mp (show Sum.inl j ∈ A.disjSum B from hj)) (fun h => hh (congr_arg _ h))
    | inr j =>
      exact he hi (inr_mem_disjSum.mp (show Sum.inr j ∈ A.disjSum B from hj))
  | inr i =>
    have hi := inr_mem_disjSum.mp (show Sum.inr i ∈ A.disjSum B from hi)
    cases j with
    | inr j =>
      exact h2 hi (inr_mem_disjSum.mp (show Sum.inr j ∈ A.disjSum B from hj)) (fun h => hh (congr_arg _ h))
    | inl j =>
      exact (he (inl_mem_disjSum.mp (show Sum.inl j ∈ A.disjSum B from hj)) hi).symm

lemma apart_separated (X : ι → Support n) (s : Finset ι) :
    Apart X s ↔ Gas.separated (blocked X) s := by
  constructor
  · rintro h i hi j hj he (hh|⟨x,hx,h⟩)
    · exact he hh
    rename_i z
    exact Finset.disjoint_left.mp (z hi hj he) hx h
  intro h i hi j hj he
  exact Finset.disjoint_left.mpr fun x hx hX => h i hi j hj he (Or.inr ⟨x,hx,hX⟩)

theorem split_term (X : ι → Support n) (Y I : κ → Support n) (D : Support n)
    (w : ι → ℝ) (d : κ → ℝ) (A : Finset κ) (B : Finset ι) :
    gasTerm (both Y X) (onlyL I) D (Sum.elim d w) (A.disjSum B) =
      gasTerm Y I D d A * Gas.value (blocked X) (Gas.cut X (A.biUnion Y) w) B := by
  have he : (A.disjSum B).biUnion (onlyL I) = A.biUnion I := by
    rw [disj_union]; simp
  unfold gasTerm Records Gas.value
  rw [he, apart_split, apart_separated X]
  by_cases hl : Apart Y A ∧ A.biUnion I = D
  · rw [if_pos hl]; by_cases hh : Gas.separated (blocked X) B
    · rw [if_pos hh]; by_cases hz : ∀ j∈B, Disjoint (A.biUnion Y) (X j)
      · rw [if_pos ⟨⟨hl.1,hh,hz⟩,hl.2⟩,prod_disjSum]
        simp only [Sum.elim_inl,Sum.elim_inr]; congr 1
        exact prod_congr rfl fun j hj => (if_pos (hz _ hj)).symm
      push Not at hz
      obtain ⟨j,hj,ht⟩ := hz
      rw [if_neg (fun hc => ht (hc.1.2.2 j hj)),prod_eq_zero hj (show Gas.cut X (A.biUnion Y) w j = 0 from if_neg ht),mul_zero]
    rw [if_neg hh, mul_zero, if_neg (fun h => hh h.1.2.1)]
  rw [if_neg hl, zero_mul, if_neg (fun h => hl ⟨h.1.1,h.2⟩)]

lemma gas_absolute (X I : ι → Support n) (D : Support n) (w : ι → ℝ) (h : Summable fun i => ‖w i‖) :
    Summable (fun s => ‖gasTerm X I D w s‖) := by
  apply (summable_finsetProd_of_summable_nonneg (fun i => norm_nonneg (w i)) h).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro s
  unfold gasTerm; split
  · rw [norm_prod]
  rw [norm_zero]; exact prod_nonneg fun _ _ => norm_nonneg _

lemma joint_absolute {ι κ : Type*} (w : ι → ℝ) (d : κ → ℝ) (h : Summable fun i => ‖w i‖) (k : Summable fun i => ‖d i‖) :
    Summable (fun i => ‖Sum.elim d w i‖) := by
  rw [show (fun i => ‖Sum.elim d w i‖) = Sum.elim (fun i => ‖d i‖) (fun i => ‖w i‖) by
    funext i; cases i <;> rfl]
  exact Summable.sum _ k h

/-- The term weights needn't be themselves small (before attempting
the log), e.g. it's enough here to receive absolute spell costs with
their first-system proof. -/
lemma unforce (X : ι → Support n) (Y I : κ → Support n) (D : Support n)
    (w : ι → ℝ) (d : κ → ℝ)
    (he : Summable (fun s => ‖gasTerm (both Y X) (onlyL I) D (Sum.elim d w) s‖)) :
    let f (A : Finset κ) := gasTerm Y I D d A * Gas.total (blocked X) (Gas.cut X (A.biUnion Y) w)
    Summable (fun A => ‖f A‖) ∧
    (∑' s,gasTerm (both Y X) (onlyL I) D (Sum.elim d w) s) = ∑' A,f A := by
  intro f
  let e := setSplit (ι:=ι) (κ:=κ)
  let H := gasTerm (both Y X) (onlyL I) D (Sum.elim d w)
  have hf : Summable (fun i => ‖H (e i)‖) := Equiv.summable_iff e (f:=fun i => ‖H i‖) |>.mpr he
  have hh (A : Finset κ) : (∑' B : Finset ι, H (e (A,B))) = f A := by
    unfold f; rw [Gas.total, ← tsum_mul_left]; exact tsum_congr fun B => split_term X Y I D w d A B
  refine ⟨?_,(e.tsum_eq H).symm.trans (hf.of_norm.tsum_prod.trans (tsum_congr hh))⟩
  obtain ⟨hx,hz⟩ := (summable_prod_of_nonneg (f:=fun i => ‖H (e i)‖) fun _ => norm_nonneg _).mp hf
  apply hz.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i; rw [← hh]; exact norm_tsum_le_tsum_norm (hx i)

lemma ready_absolute (X : ι → Support n) (w : ι → ℝ) (hn : ∀ i, (X i).Nonempty)
    (B : ℕ) {a γ δ q : ℝ} (ha : 0 ≤ a)
    (h : Trees.Ready X B (fun i => ‖w i‖) a γ δ q) : Summable (fun i => ‖w i‖) := by
  let f (i : ι) := ‖w i‖
  have he := AbsoluteSums.Product.everyone_ne X B (show ∀ i,0 ≤ f i from fun _ => norm_nonneg _)
    (fun i _ => hn i) h.2.2.2.2.2
  apply he.2.1.of_nonneg_of_le (fun i => norm_nonneg _)
  intro i
  have ht := h.2.1
  exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg (add_nonneg ha ht.le) (by positivity)))

/-- Exact charge for the *actual* restriction in the first gas. -/
def omission (X : ι → Support n) (Y : κ → Support n) (w : ι → ℝ) (A : Finset κ) : ℝ :=
  ∑' z, Gas.missing X (A.biUnion Y) w z

def residual (X : ι → Support n) (Y I : κ → Support n) (D : Support n)
    (w : ι → ℝ) (d : κ → ℝ) (A : Finset κ) :=
  gasTerm Y I D d A * Real.exp (- omission X Y w A)

/-- Covered disjoint gas identity to second-log+forced-expansion form.
No logarithm taken of the whole covered sum. True exponential leading
factor, with **positive** sign (effective *action* includes the negative
log). Every rhs series absolutely convergent (incl the individual
exclusion charges). -/
theorem exclusion (X : ι → Support n) (Y I : κ → Support n) (D : Support n)
    (w : ι → ℝ) (d : κ → ℝ) (hk : Summable fun i => ‖d i‖) (hn : ∀ i, (X i).Nonempty)
    (B : ℕ) {a γ δ q : ℝ} (ha : 0 ≤ a) (h : Trees.Ready X B (fun i => ‖w i‖) a γ δ q) :
    let R := blocked X
    let full := gasTerm (both Y X) (onlyL I) D (Sum.elim d w)
    let rest := residual X Y I D w d
    let bulk := Real.exp (Gas.logSum R w)
    Summable (fun i => ‖full i‖) ∧
    Summable (fun i => ‖Gas.term R w i‖) ∧
    (∀ A : Finset κ, Summable (fun z => ‖Gas.missing X (A.biUnion Y) w z‖)) ∧
    Summable (fun i => ‖rest i‖) ∧
    (∑' s, full s) = bulk * ∑' A, rest A := by
  have hw := ready_absolute X w hn B ha h
  intro R full rest bulk
  have hF : Summable _ := gas_absolute (both Y X) (onlyL I) D _ (joint_absolute w d hw hk)
  have hf := unforce X Y I D w d hF
  have hh := Gas.price_log R w ⟨fun i => Or.inl rfl,fun _ _ => blocked_back X⟩ X B (literal_test X hn) ha h
  have ht (A : Finset κ) : gasTerm Y I D d A * Gas.total R (Gas.cut X (A.biUnion Y) w) = bulk * rest A := by
    rw [(Gas.restores_log X (A.biUnion Y) B w hn ha h).1,← hh.2.2.1]
    unfold rest bulk residual omission R; ring
  have hp := hf.1
  change Summable (fun (i : Finset κ) => ‖gasTerm Y I D d i * Gas.total R (Gas.cut X (i.biUnion Y) w)‖) at hp
  simp_rw [ht, norm_mul] at hp
  have he : 0<bulk := Real.exp_pos _
  refine ⟨hF,hh.2.1.2.1,?_,?_,hf.2.trans ?_⟩
  · intro A
    apply hh.2.1.2.1.of_nonneg_of_le (fun _ => norm_nonneg _); intro x
    unfold Gas.missing; split
    · rw [norm_zero]; exact norm_nonneg _
    exact le_rfl
  · apply (hp.mul_left ‖bulk‖⁻¹).congr
    intro i; rw [← mul_assoc,inv_mul_cancel₀ (norm_ne_zero_iff.mpr he.ne'),one_mul]
  rw [← tsum_mul_left]; exact tsum_congr ht

end YM.Push.LogIdentity
