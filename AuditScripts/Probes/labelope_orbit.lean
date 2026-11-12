import ChallengeSpec

/-! Audit probe (follow-up: translation-dependent label action vs. OPE).

(A) `Reconstructed.covers` + `Hierarchy.fieldFinite`: the label space has rank at most `ℵ₀`.
(B) The coordinate group law gives `g * T a = T (Λ_g a) * g`.
(C) With `W2.labelComposition`, a translation eigenlabel `ψ` (character `χ`) is carried by
    `onLabels g` to a translation eigenlabel with character `b ↦ χ (Λ_g⁻¹ b)`.
(D) Hence, inside any `Reconstructed` hierarchy, the Lorentz orbit of the character of a
    nonzero translation eigenlabel is countable. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.AuditLabelOrbit
open YangMills Function Set Cardinal

theorem apply_inv_apply (L : (Spacetime →L[ℝ] Spacetime)ˣ) (x : Spacetime) :
    L.val ((L⁻¹).val x) = x := by
  have h := congrArg (fun T : Spacetime →L[ℝ] Spacetime => T x) (Units.mul_inv L)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

section A
variable {g : GaugeGroup} {C : WilsonFamily g}

/-- (A) `covers` forces countable rank of the label space. -/
theorem rank_labels_le (T : Hierarchy C) (hR : T.Reconstructed) :
    Module.rank ℂ T.labels.carrier ≤ ℵ₀ := by
  classical
  have hs : (⋃ d : ℕ, T.toLabel d '' Set.range (Module.finBasis ℂ (T.Field d))).Countable :=
    Set.countable_iUnion fun d => ((Set.finite_range _).image _).countable
  have hspan : Submodule.span ℂ
      (⋃ d : ℕ, T.toLabel d '' Set.range (Module.finBasis ℂ (T.Field d))) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨⟨d, v⟩, rfl⟩ := hR.covers x
    have hv : v ∈ Submodule.span ℂ (Set.range (Module.finBasis ℂ (T.Field d))) := by
      rw [(Module.finBasis ℂ (T.Field d)).span_eq]; trivial
    have hx : T.toLabel d v ∈
        Submodule.span ℂ (T.toLabel d '' Set.range (Module.finBasis ℂ (T.Field d))) := by
      rw [Submodule.span_image]
      exact Submodule.mem_map_of_mem hv
    exact Submodule.span_mono
      (Set.subset_iUnion (fun d : ℕ => T.toLabel d '' Set.range (Module.finBasis ℂ (T.Field d))) d) hx
  calc Module.rank ℂ T.labels.carrier
      = Module.rank ℂ (⊤ : Submodule ℂ T.labels.carrier) := (rank_top ℂ T.labels.carrier).symm
    _ = Module.rank ℂ (Submodule.span ℂ
          (⋃ d : ℕ, T.toLabel d '' Set.range (Module.finBasis ℂ (T.Field d)))) := by rw [hspan]
    _ ≤ #(⋃ d : ℕ, T.toLabel d '' Set.range (Module.finBasis ℂ (T.Field d))) := rank_span_le _
    _ ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr hs
end A

section BC
variable {H : HilbertSpace} {Labels : FieldLabels}

theorem coords_ext (P : PoincareAction H Labels) {g h : P.Symmetry}
    (h1 : (P.coordinates g).1.val = (P.coordinates h).1.val)
    (h2 : (P.coordinates g).2 = (P.coordinates h).2) : g = h :=
  P.coordinates.injective (Prod.ext (Subtype.ext h1) h2)

/-- (B) Conjugating a translation by any symmetry. -/
theorem conj_translation (P : PoincareAction H Labels) (g : P.Symmetry) (a : Spacetime) :
    g * P.pureTranslation a =
      P.pureTranslation ((P.coordinates g).1.val.val a) * g := by
  apply coords_ext P
  · rw [(P.productCoordinates g (P.pureTranslation a)).1,
      (P.productCoordinates (P.pureTranslation ((P.coordinates g).1.val.val a)) g).1,
      (P.translationCoordinates a).1,
      (P.translationCoordinates ((P.coordinates g).1.val.val a)).1, mul_one, one_mul]
  · rw [(P.productCoordinates g (P.pureTranslation a)).2,
      (P.productCoordinates (P.pureTranslation ((P.coordinates g).1.val.val a)) g).2,
      (P.translationCoordinates a).2,
      (P.translationCoordinates ((P.coordinates g).1.val.val a)).1,
      (P.translationCoordinates ((P.coordinates g).1.val.val a)).2,
      Units.val_one, one_apply_eq_self, add_comm]

/-- (C) Transport of a translation eigenlabel by `onLabels g`. -/
theorem eigen_transport (T : WightmanTheory H Labels) (hW2 : T.W2)
    (ψ : Labels.carrier) (χ : Spacetime → ℂ)
    (hχ : ∀ a, T.poincare.onLabels (T.poincare.pureTranslation a) ψ = χ a • ψ)
    (g : T.poincare.Symmetry) (b : Spacetime) :
    T.poincare.onLabels (T.poincare.pureTranslation b) (T.poincare.onLabels g ψ) =
      χ (((T.poincare.coordinates g).1.val⁻¹).val b) • T.poincare.onLabels g ψ := by
  have key : ∀ a, T.poincare.onLabels
      (T.poincare.pureTranslation ((T.poincare.coordinates g).1.val.val a))
      (T.poincare.onLabels g ψ) = χ a • T.poincare.onLabels g ψ := by
    intro a
    rw [← hW2.labelComposition, ← conj_translation, hW2.labelComposition, hχ, map_smul]
  have h := key (((T.poincare.coordinates g).1.val⁻¹).val b)
  rwa [apply_inv_apply] at h
end BC

section D
variable {g : GaugeGroup} {C : WilsonFamily g}

/-- (D) In a `Reconstructed` hierarchy the Lorentz orbit of the translation character of a
nonzero eigenlabel is countable. -/
theorem orbit_countable (T : Hierarchy C) (hR : T.Reconstructed)
    (ψ : T.labels.carrier) (hψ : ψ ≠ 0) (χ : Spacetime → ℂ)
    (hχ : ∀ a, T.theory.poincare.onLabels (T.theory.poincare.pureTranslation a) ψ = χ a • ψ) :
    (Set.range fun g : T.theory.poincare.Symmetry =>
      fun b : Spacetime => χ (((T.theory.poincare.coordinates g).1.val⁻¹).val b)).Countable := by
  classical
  let f : Spacetime → Module.End ℂ T.labels.carrier :=
    fun b => (T.theory.poincare.onLabels (T.theory.poincare.pureTranslation b)).toLinearMap
  have hcomm : ∀ a b, Commute (f a) (f b) := by
    intro a b
    show f a * f b = f b * f a
    refine LinearMap.ext fun x => ?_
    show T.theory.poincare.onLabels (T.theory.poincare.pureTranslation a)
        (T.theory.poincare.onLabels (T.theory.poincare.pureTranslation b) x) =
      T.theory.poincare.onLabels (T.theory.poincare.pureTranslation b)
        (T.theory.poincare.onLabels (T.theory.poincare.pureTranslation a) x)
    rw [← hR.axioms.w2.labelComposition, ← hR.axioms.w2.labelComposition,
      ← T.theory.poincare.translationAdd, ← T.theory.poincare.translationAdd, add_comm]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  have hpick : ∀ c : (Set.range fun g : T.theory.poincare.Symmetry =>
        fun b : Spacetime => χ (((T.theory.poincare.coordinates g).1.val⁻¹).val b)),
      ∃ v : T.labels.carrier, v ≠ 0 ∧ v ∈ ⨅ b, (f b).maxGenEigenspace (c.1 b) := by
    rintro ⟨_, g, rfl⟩
    refine ⟨T.theory.poincare.onLabels g ψ, (LinearEquiv.map_ne_zero_iff _).mpr hψ, ?_⟩
    rw [Submodule.mem_iInf]
    intro b
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    exact eigen_transport T.theory hR.axioms.w2 ψ χ hχ g b
  choose v hv0 hvmem using hpick
  have hli : LinearIndependent ℂ v :=
    (hind.comp Subtype.val_injective).linearIndependent _ hvmem hv0
  exact Cardinal.mk_le_aleph0_iff.mp (hli.cardinal_le_rank.trans (rank_labels_le T hR))
end D

#print axioms rank_labels_le
#print axioms conj_translation
#print axioms eigen_transport
#print axioms orbit_countable

end YangMills.AuditLabelOrbit
