import YM.Bid.Phase
import YM.OS.Halves


/-!
# Padding from Bench

This follows the priced/irons argument in YM.OS.Halves, but needs to use Bench's
(even just existential) sub-width, rather than their Tiled hypothesis. Only the
slab, ordering and QRead at the sub-width are needed from Bench, not why/how b
was selected.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.B01
open YM.OS
open scoped NNReal

variable {G : Gauge} {C : Family G} {S : Table C.book}

-- First the cost for each test, independently of choosing any single Spread
private lemma with_cost (V : Chamber S timeAxis) (hv : S.Hierarchy)
    (bench : Bid.Bench C S) (D : ℕ) (R : ℝ) :
    ∃ C₀ : ℝ, ∃ A : ℕ, 0 < C₀ ∧ ∀ w : C.book.Word, ∀ d : ℝ≥0,
      constrained D R w → ∀ h : Slab timeAxis d w, ∀ r : ℝ, 0 < r → r ≤ 1 →
      buffer timeAxis r d w → ∃ T : V.GNS.H.Op, ‖T‖ ≤ Spread.radius C₀ A w r ∧
        ∀ x, T (V.GNS.plant x) = V.GNS.plant (entering h x) := by
  obtain ⟨C₀, A, hC, useBench⟩ := bench D R
  refine ⟨C₀, A, hC, fun w d cons hd r hr hr' buf => ?_⟩
  rcases eq_or_ne w [] with hnil|hne
  · subst w
    exact ⟨V.flow.E d, by simpa [Spread.radius] using V.flow.shrinks d,
      fun x => (V.atBirth d x).symm⟩
  obtain ⟨_, s, hsd, _, hs, hQ⟩ := useBench d w hne cons hd r hr hr' buf
  have hpos : 0 < Spread.radius C₀ A w r := by
    have hw : 0 < w.length := Nat.pos_of_ne_zero (fun h => hne (List.length_eq_zero_iff.mp h))
    unfold Spread.radius
    positivity
  obtain ⟨P, hP, hRead⟩ := producer V hs hv hQ hpos
  -- Forward time by the *remaining* width, THEN use the s operator.
  refine ⟨P.comp (V.flow.E (d-s)), (ContinuousLinearMap.opNorm_comp_le ..).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (V.flow.shrinks _)).trans hP), fun x => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ← V.atBirth, hRead]
  congr 1
  apply Subtype.ext
  change linked timeAxis _ w _ = linked timeAxis _ w _
  simp only [linked, travel, raised, paths]
  rw [← add_smul, ← NNReal.coe_add, tsub_add_cancel_of_le hsd]

theorem answer : YM.Bid.B01 := by
  classical
  intro G C S V hier bench
  have hex (d : ℝ≥0) (w : C.book.Word) :
      ∃ T : V.GNS.H.Op, ∀ h : Slab timeAxis d w, ∀ x,
        T (V.GNS.plant x) = V.GNS.plant (entering h x) := by
    by_cases h : Slab timeAxis d w
    · obtain ⟨D, R, hc, r, hr, hr', hb⟩ := affordable h
      obtain ⟨_, _, _, useCost⟩ := with_cost V hier bench D R
      obtain ⟨T, _, hT⟩ := useCost w d hc h r hr hr' hb
      exact ⟨T, fun _ => hT⟩
    exact ⟨0, fun h' => (h h').elim⟩
  choose T hT using hex
  let A : Spread V := ⟨T, fun h => hT _ _ h⟩
  refine ⟨A, fun D R => ?_⟩
  obtain ⟨C₀, K, hp, useCost⟩ := with_cost V hier bench D R
  refine ⟨C₀, K, hp, fun w d hc h r hr hr' hb => ?_⟩
  -- The possibly differently found operator equals A.place on the plants.
  obtain ⟨P, hP, H⟩ := useCost w d hc h r hr hr' hb
  have hEq : A.place d w = P := V.GNS.by_bud (fun x => (A.reads h x).trans (H x).symm)
  rw [hEq]
  exact hP
end YM.Work.B01
