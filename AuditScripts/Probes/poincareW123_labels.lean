import ChallengeSpec

/-! Audit probe 2 (group: Lorentz group, Poincare action, W1-W3 assembly).
(a) the pullback composes as a left action, consistently with `labelComposition`;
(b) with `Faithful`, `onLabels g` is uniquely determined by `onStates g` and the fields;
(c) `TraceTest.centered` holds trivially when `centeredTrace = 0`. -/

set_option autoImplicit false
noncomputable section
open YangMills

namespace YangMills.AuditPoincare2

abbrev IsPL (L : (Spacetime →L[ℝ] Spacetime)ˣ) : Prop :=
  LinearMap.det L.val.toLinearMap = 1 ∧
  (∀ x, minkowskiSquare (L.val x) = minkowskiSquare x) ∧
  (∀ x, L.val x ∈ forwardCone ↔ x ∈ forwardCone)

theorem apply_inv_apply (L : (Spacetime →L[ℝ] Spacetime)ˣ) (x : Spacetime) :
    L.val ((L⁻¹).val x) = x := by
  have h := congrArg (fun T : Spacetime →L[ℝ] Spacetime => T x) (Units.mul_inv L)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

theorem inv_apply_apply (L : (Spacetime →L[ℝ] Spacetime)ˣ) (x : Spacetime) :
    (L⁻¹).val (L.val x) = x := by
  have h := congrArg (fun T : Spacetime →L[ℝ] Spacetime => T x) (Units.inv_mul L)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

theorem isPL_inv {L : (Spacetime →L[ℝ] Spacetime)ˣ} (hL : IsPL L) : IsPL L⁻¹ := by
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · have h2 : LinearMap.det
        (((L⁻¹).val * L.val : Spacetime →L[ℝ] Spacetime)).toLinearMap = 1 := by
      rw [Units.inv_mul]
      exact LinearMap.det_id
    rwa [ContinuousLinearMap.toLinearMap_mul, map_mul, hL.1, mul_one] at h2
  · have h := hL.2.1 ((L⁻¹).val x)
    rw [apply_inv_apply] at h
    exact h.symm
  · have h := hL.2.2 ((L⁻¹).val x)
    rw [apply_inv_apply] at h
    exact h.symm

def plInv (a : ProperLorentz) : ProperLorentz := ⟨a.val⁻¹, isPL_inv a.2⟩

variable {H : HilbertSpace} {Labels : FieldLabels}

theorem coords_ext (P : PoincareAction H Labels) {g h : P.Symmetry}
    (h1 : (P.coordinates g).1.val = (P.coordinates h).1.val)
    (h2 : (P.coordinates g).2 = (P.coordinates h).2) : g = h :=
  P.coordinates.injective (Prod.ext (Subtype.ext h1) h2)

theorem lor_mul (P : PoincareAction H Labels) (g h : P.Symmetry) :
    (P.coordinates (g * h)).1.val = (P.coordinates g).1.val * (P.coordinates h).1.val :=
  (P.productCoordinates g h).1

theorem tr_mul (P : PoincareAction H Labels) (g h : P.Symmetry) :
    (P.coordinates (g * h)).2 =
      (P.coordinates g).1.val.val (P.coordinates h).2 + (P.coordinates g).2 :=
  (P.productCoordinates g h).2

def symInv (P : PoincareAction H Labels) (g : P.Symmetry) : P.Symmetry :=
  P.coordinates.symm (plInv (P.coordinates g).1,
    -(((P.coordinates g).1.val⁻¹).val (P.coordinates g).2))

theorem mul_symInv (P : PoincareAction H Labels) (g : P.Symmetry) :
    g * symInv P g = 1 := by
  apply coords_ext P
  · rw [lor_mul, symInv, Homeomorph.apply_symm_apply, P.identityCoordinates.1]
    exact mul_inv_cancel _
  · rw [tr_mul, symInv, Homeomorph.apply_symm_apply, P.identityCoordinates.2]
    show (P.coordinates g).1.val.val (-(((P.coordinates g).1.val⁻¹).val (P.coordinates g).2)) +
      (P.coordinates g).2 = 0
    rw [map_neg, apply_inv_apply, neg_add_cancel]

theorem onTests_one (P : PoincareAction H Labels) (f : TestFunction) :
    P.onTests 1 f = f := by
  ext x
  rw [P.pullback, P.identityCoordinates.2, sub_zero, P.identityCoordinates.1, inv_one,
    Units.val_one, one_apply_eq_self]

/-! (a) Left-action law of the pullback: `onTests (g * h) = onTests g ∘ onTests h`. -/
theorem onTests_mul (P : PoincareAction H Labels) (g h : P.Symmetry) (f : TestFunction) :
    P.onTests (g * h) f = P.onTests g (P.onTests h f) := by
  ext x
  rw [P.pullback, P.pullback, P.pullback, lor_mul, tr_mul, mul_inv_rev, Units.val_mul,
    mul_apply_eq_comp,
    show x - ((P.coordinates g).1.val.val (P.coordinates h).2 + (P.coordinates g).2) =
      (x - (P.coordinates g).2) - (P.coordinates g).1.val.val (P.coordinates h).2 by abel,
    map_sub, inv_apply_apply]

theorem onTests_surj (P : PoincareAction H Labels) (g : P.Symmetry) (f : TestFunction) :
    ∃ f' : TestFunction, P.onTests g f' = f :=
  ⟨P.onTests (symInv P g) f, by rw [← onTests_mul, mul_symInv, onTests_one]⟩

theorem domain_surj (T : WightmanTheory H Labels) (hW2 : T.W2) (g : T.poincare.Symmetry)
    (ψ : T.fields.domain) :
    ∃ χ : T.fields.domain,
      (⟨T.poincare.onStates g χ.1, hW2.domainInvariant g χ.2⟩ : T.fields.domain) = ψ := by
  refine ⟨⟨T.poincare.onStates (symInv _ g) ψ.1, hW2.domainInvariant _ ψ.2⟩, Subtype.ext ?_⟩
  show T.poincare.onStates g (T.poincare.onStates (symInv _ g) ψ.1) = ψ.1
  have h := congrArg (fun A : H.Operator => A ψ.1) (T.poincare.composition g (symInv _ g))
  simp only [mul_symInv, T.poincare.identity, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at h
  exact h.symm

/-! (b) Uniqueness: any linear label map satisfying the covariance law at `g`
equals `onLabels g`, once the fields are faithful. -/
theorem onLabels_unique (T : WightmanTheory H Labels) (hW2 : T.W2) (hF : T.fields.Faithful)
    (g : T.poincare.Symmetry) (M : Labels.carrier →ₗ[ℂ] Labels.carrier)
    (hM : ∀ (label : Labels.carrier) (test : TestFunction) (state : T.fields.domain),
      T.poincare.onStates g (T.fields.field label test state).1 =
        (T.fields.field (M label) (T.poincare.onTests g test)
          ⟨T.poincare.onStates g state.1, hW2.domainInvariant g state.2⟩).1)
    (ℓ : Labels.carrier) : M ℓ = T.poincare.onLabels g ℓ := by
  by_contra hne
  obtain ⟨f, hf⟩ := hF _ (sub_ne_zero.mpr hne)
  apply hf
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨f', rfl⟩ := onTests_surj T.poincare g f
  obtain ⟨χ, rfl⟩ := domain_surj T hW2 g ψ
  have key : T.fields.field (M ℓ) (T.poincare.onTests g f')
        ⟨T.poincare.onStates g χ.1, hW2.domainInvariant g χ.2⟩ =
      T.fields.field (T.poincare.onLabels g ℓ) (T.poincare.onTests g f')
        ⟨T.poincare.onStates g χ.1, hW2.domainInvariant g χ.2⟩ :=
    Subtype.ext ((hM ℓ f' χ).symm.trans (hW2.fieldCovariance g ℓ f' χ))
  rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, key, sub_self, LinearMap.zero_apply]

/-! (c) A zero centered trace makes `TraceTest.centered` automatic. -/
theorem centered_of_zero {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
    (h0 : T.centeredTrace = 0) (f : TestFunction) :
    inner ℂ T.theory.fields.vacuum.1
      (T.theory.fields.field (T.toLabel 4 T.centeredTrace) f T.theory.fields.vacuum).1 = 0 := by
  rw [h0]
  simp

#print axioms onTests_mul
#print axioms onLabels_unique
#print axioms centered_of_zero

end YangMills.AuditPoincare2
