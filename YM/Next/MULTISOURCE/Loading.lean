import YM.Next.MULTISOURCE.Cargo

/-!
# Flags and complete supports for multi-marker initialization
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Marker MeasureTheory Filter Function Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {n : Side} {V : Type} [DecidableEq V] [Fintype V] {G : Gauge}

lemma sufficient {t : ℝ} {D X : Support n} {U W : Config G n} (h : X ⊆ D)
    (hh : D∩ flags t U=D∩flags t W) : X ∩ flags t U=X ∩flags t W := calc
  _ = X ∩ (D∩flags t U) := by rw [← Finset.inter_assoc,inter_eq_left.mpr h]
  _ = X ∩flags t W := by rw [hh, ← Finset.inter_assoc,inter_eq_left.mpr h]

namespace Couples

/-- A complement payload (must find a flag). -/
structure Weight (P : BudgetPoint) (X : Support n) (F : Config G n → ℂ) : Prop where
  meas : Measurable F
  gauge : GaugeInvariant F
  reads : UsesFinal P.threshold X F
  needs U : F U≠0 → ∃ i∈X,i∈flags P.threshold U

variable (P : Rep G n) (Y : V → Support n) (F : V→Config G n→ℂ) (T : Finset V)

omit [DecidableEq V] in
lemma designated (q : Pack n) (j : Recipe n V) (h : j∈trays Y q) (hb : P.activities.ForcedFamily P.p)
    (hk : ∀ i,Weight P.p (Y i) (F i)) :
    Legible P.p q (fun U => earning Y (flags P.p.threshold U) (master P F U) j) := by
  obtain ⟨hx,hX⟩ := mem_filter.mp h
  have he : ground Y j=q.zone := (merged_zone Y hx).symm.trans (congrArg Pack.zone hX)
  have ht : tags j=q.flagsAt := (merged_tags Y hx).symm.trans (congrArg Pack.flagsAt hX)
  have hi (i) (hi : i∈ j) : span Y i ⊆ q.zone := by
    rw [← he]; exact Finset.subset_biUnion_of_mem (span Y) hi
  unfold earning; simp_rw [he, ht]
  constructor
  · refine Measurable.ite (Pack.neighborhood_meas q _) (Finset.measurable_fun_prod _
      (fun i H => ?_)) measurable_const
    cases i with
    | inl i => exact (incumbent_legible P i hb).borel
    | inr i => exact (hk i).meas
  · intro i U
    simp only [gauge_flags]; split
    · refine prod_congr rfl fun a ha => ?_
      cases a with
      | inl a => exact (incumbent_legible P a hb).symmetry _ _
      | inr a => exact (hk a).gauge _ _
    rfl
  · intro U W hH hu
    change (if _ then _ else _) = (if _ then _ else _)
    rw [hu]; split
    · refine prod_congr rfl fun a ha => ?_
      have hh := agrees_mono hH (Finset.coe_subset.mpr (hi a ha))
      have hv := sufficient (hi a ha) hu
      cases a with
      | inl a => exact (incumbent_legible P a hb).reads U W hh hv
      | inr a => exact (hk a).reads U W hh hv
    rfl
  intro U hN; split at hN; assumption; exact False.elim (hN rfl)

lemma pay_legible (q : Pack n) (hb : P.activities.ForcedFamily P.p)
    (hk : ∀ i,Weight P.p (Y i) (F i)) : Legible P.p q (payload Y P F T q) := by
  unfold payload
  let W j U := earning Y (flags P.p.threshold U) (master P F U) j
  suffices H : ∀ L : Finset (Recipe n V), L ⊆ trays Y q →
      Legible P.p q (fun U => ∑ b∈L,W b U) from H _ (Finset.filter_subset ..)
  intro L; induction L using Finset.induction with
  | empty => intro H; simp_rw [Finset.sum_empty]; exact Legible.zero P.p q
  | insert i L h ih =>
    intro hi; obtain ⟨hx,H⟩ := Finset.insert_subset_iff.mp hi
    simp_rw [Finset.sum_insert h]; exact (designated P Y F q i hx hb hk).add (ih H)

lemma zone_of_payload (o : V → Site n) (H : ∀ i, o i∈Y i) (q : Pack n)
    (h : payload Y P F T q ≠ 0) : T.image o ⊆ q.zone := by
  by_contra he
  apply h; funext U
  apply Finset.sum_eq_zero; intro i hi
  obtain ⟨hv,hT⟩ := Finset.mem_filter.mp hi
  obtain ⟨hx,hX⟩ := mem_filter.mp hv
  refine False.elim (he ?_)
  rw [← hX,merged_zone Y hx,← hT]
  intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
  exact mem_biUnion.mpr ⟨Sum.inr k, mem_toRight.mp hk,H k⟩
end Couples
end YM.Multi
