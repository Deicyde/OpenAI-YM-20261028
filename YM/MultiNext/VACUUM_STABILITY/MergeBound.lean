import YM.MultiNext.VACUUM_STABILITY.BulkGas
import YM.MultiNext.VACUUM_STABILITY.MergeValue

set_option warningAsError false

/-!
# Forced merger price

Cylindrical/stamped terms and absolute hit bound even at the post-integration stage where
missing clusters can attach to several d and have unlimited repeat powers. Restores one κ
saving per merged component. Does not extend to unestimable K from vacuum equality alone.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Rejoin
open RG Lattice Wilson Filter Finset Function MeasureTheory Text  Syllable Corona Alternatives
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {I J : Type*} {n : Side} {G : Gauge}

/-- Complete-support activity dependencies, including final flag halo convention; no value
condition here, so can model omitted clusters even if they need meet a pack to be selected. -/
structure Spanned (P : BudgetPoint) (Y : Support n) (u : Config G n → ℂ) : Prop where
  meas : Measurable u
  gauge : GaugeInvariant u
  reads : UsesFinal P.threshold Y u

namespace Spanned
variable {P : BudgetPoint} {Y : Support n} {u : Config G n → ℂ}

lemma regular (h : P.Regular Y u) : Spanned P Y (masked P.threshold Y u) := by
  refine ⟨masked_measurable _ _ _ h.borel,fun k U => ?_,fun U V he ht => ?_⟩
  · have he : Healthy P.threshold Y (Lattice.gauge k U) ↔ Healthy P.threshold Y U := by simp [Healthy]
    by_cases H : Healthy P.threshold Y U
    · simp only [masked_eq _ _ _ _ H,masked_eq _ _ _ _ (he.mpr H),h.symmetry k U]
    rw [masked_ne _ _ _ _ (fun h => H (he.mp h)), masked_ne _ _ _ _ H]
  have hx : Healthy P.threshold Y U ↔ Healthy P.threshold Y V := by unfold Healthy; rw [disjoint_iff_inter_eq_empty,ht];
                                                                        rw [disjoint_iff_inter_eq_empty]
  by_cases hd : Healthy P.threshold Y U
  · rw [masked_eq _ _ _ _ hd,masked_eq _ _ _ _ (hx.mp hd)]; exact h.sites U V he
  rw [masked_ne _ _ _ _ hd, masked_ne _ _ _ _ (fun he => hd (hx.mpr he))]

lemma larger (h : Spanned P Y u) (Z : Support n) (hZ : Y ⊆ Z) : Spanned P Z u := by
  refine ⟨h.meas,h.gauge,fun U V he ht => h.reads U V (agrees_mono he hZ) ?_⟩
  rw [← inter_eq_left.mpr hZ, inter_assoc, inter_assoc, ht]

lemma legible {q : Pack n} (h : Legible P q u) : Spanned P q.zone u := ⟨h.borel,h.symmetry,h.reads⟩

lemma negate (h : Spanned P Y u) : Spanned P Y (-u) := ⟨h.meas.neg,
  fun k U => congrArg (-·) (h.gauge k U), fun U V he ht => congrArg (-·) (h.reads U V he ht)⟩

lemma raised (h : Spanned P Y u) (j : ℕ) : Spanned P Y (fun U => spice (u U) j) := ⟨measurable_const.mul (h.meas.pow_const _),
  fun k U => by rw [h.gauge k U],fun U V he ht => by rw [h.reads U V he ht]⟩
end Spanned

namespace Hearth
variable (D : Hearth n I J)

lemma remap_pass (P : BudgetPoint) (f : I → Config G n → ℂ) (g : J → Config G n → ℂ)
    (hf : ∀ i, Legible P (D.pack i) (f i)) (hg : ∀ i, Spanned P (D.sites i) (g i)) (p : D.Piece) :
    Legible P (D.remap p) fun U => D.embers (flags P.threshold U)
      (Sum.elim (fun i => f i U) (heat fun i => g i U)) p := by
  let H U := Sum.elim (fun i => f i U) (heat fun i => g i U)
  have he k (hk : k∈p.val) : Spanned P (D.ground p.val) (fun U => H U k) := by
    refine Spanned.larger (Y:=D.span k) ?_ _ (fun _ hx => Finset.mem_biUnion.mpr ⟨k,hk,hx⟩)
    cases k with
    | inl i => exact Spanned.legible (hf i)
    | inr i => exact Spanned.raised (hg i.1) i.2
  refine ⟨Measurable.ite (Pack.neighborhood_meas (D.remap p) _) (Finset.measurable_fun_prod _ fun i hi =>
    (he i hi).meas) measurable_const, ?_, ?_, ?_⟩
  · intro k U; change embers D _ (H (Lattice.gauge k U)) _= _
    dsimp only [embers]; rw [gauge_flags]; split
    · exact Finset.prod_congr rfl fun i hi => (he i hi).gauge k U
    rfl
  · intro U V hx ht; change D.ground p.val ∩ _=D.ground p.val ∩ _ at ht
    dsimp only [embers]; rw [ht]; split
    · exact Finset.prod_congr rfl fun i hi => (he i hi).reads U V hx ht
    rfl
  intro U hu; by_contra ht; rw [remap_zone,remap_tags] at ht; exact hu (by unfold embers; rw [if_neg ht])






end Hearth
end YM.Multi.Vacuum.Rejoin
