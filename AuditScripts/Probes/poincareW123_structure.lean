import ChallengeSpec

/-! Audit probe (group: Lorentz group, Poincare action, W1-W3 assembly;
PublicTheory.lean lines 208-321). Each numbered check is an independent
declaration, so an error in one does not stop the later ones. -/

set_option autoImplicit false
noncomputable section
open YangMills

namespace YangMills.AuditPoincare

/-! (1) Instances actually used. -/
#synth TopologicalSpace ProperLorentz
#synth TopologicalSpace PoincareCoordinates
#synth TopologicalSpace (Spacetime →L[ℝ] Spacetime)
#synth Monoid (Spacetime →L[ℝ] Spacetime)

/-- (1a) The units topology is the operator-norm subspace topology. -/
example : Topology.IsOpenEmbedding
    (Units.val : (Spacetime →L[ℝ] Spacetime)ˣ → (Spacetime →L[ℝ] Spacetime)) :=
  Units.isOpenEmbedding_val

/-- (1b) `*` on the units is composition, `1` is the identity, `⁻¹` is a genuine inverse. -/
example (a b : (Spacetime →L[ℝ] Spacetime)ˣ) (x : Spacetime) :
    (a * b).val x = a.val (b.val x) := rfl
example (x : Spacetime) : (1 : (Spacetime →L[ℝ] Spacetime)ˣ).val x = x := rfl
example (a : (Spacetime →L[ℝ] Spacetime)ˣ) : a.val * (a⁻¹).val = 1 := Units.mul_inv a

/-! (2) Elaborated statements (instance arguments explicit where useful). -/
set_option pp.explicit true in
#check @WightmanTheory.W2.labelIdentity
#check @PoincareAction.pullback
#check @PoincareAction.productCoordinates
#check @WightmanTheory.W2.fieldCovariance
#check @FieldSystem.LocalCommutativity
#print WightmanTheory.Axioms

/-! (3) The `ProperLorentz` predicate and its closure properties. -/
abbrev IsPL (L : (Spacetime →L[ℝ] Spacetime)ˣ) : Prop :=
  LinearMap.det L.val.toLinearMap = 1 ∧
  (∀ x, minkowskiSquare (L.val x) = minkowskiSquare x) ∧
  (∀ x, L.val x ∈ forwardCone ↔ x ∈ forwardCone)

example : ProperLorentz = {L : (Spacetime →L[ℝ] Spacetime)ˣ // IsPL L} := rfl

theorem apply_inv_apply (L : (Spacetime →L[ℝ] Spacetime)ˣ) (x : Spacetime) :
    L.val ((L⁻¹).val x) = x := by
  have h := congrArg (fun T : Spacetime →L[ℝ] Spacetime => T x) (Units.mul_inv L)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

theorem isPL_one : IsPL (1 : (Spacetime →L[ℝ] Spacetime)ˣ) := by
  refine ⟨?_, fun _ => rfl, fun _ => Iff.rfl⟩
  first
  | exact LinearMap.det_id
  | simp

theorem isPL_mul {L M : (Spacetime →L[ℝ] Spacetime)ˣ} (hL : IsPL L) (hM : IsPL M) :
    IsPL (L * M) := by
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · rw [Units.val_mul, ContinuousLinearMap.toLinearMap_mul, map_mul, hL.1, hM.1, mul_one]
  · rw [Units.val_mul, mul_apply_eq_comp, hL.2.1, hM.2.1]
  · rw [Units.val_mul, mul_apply_eq_comp, hL.2.2, hM.2.2]

theorem isPL_inv {L : (Spacetime →L[ℝ] Spacetime)ˣ} (hL : IsPL L) : IsPL L⁻¹ := by
  refine ⟨?_, fun x => ?_, fun x => ?_⟩
  · have h2 : LinearMap.det
        (((L⁻¹).val * L.val : Spacetime →L[ℝ] Spacetime)).toLinearMap = 1 := by
      rw [Units.inv_mul]
      first
      | exact LinearMap.det_id
      | simp
    rwa [ContinuousLinearMap.toLinearMap_mul, map_mul, hL.1, mul_one] at h2
  · have h := hL.2.1 ((L⁻¹).val x)
    rw [apply_inv_apply] at h
    exact h.symm
  · have h := hL.2.2 ((L⁻¹).val x)
    rw [apply_inv_apply] at h
    exact h.symm

def plOne : ProperLorentz := ⟨1, isPL_one⟩
def plMul (a b : ProperLorentz) : ProperLorentz := ⟨a.val * b.val, isPL_mul a.2 b.2⟩
def plInv (a : ProperLorentz) : ProperLorentz := ⟨a.val⁻¹, isPL_inv a.2⟩

/-! (4) PT = -1 has determinant 1 (dimension 4) and keeps the Minkowski square;
only the cone clause removes it. -/
theorem spatial_single_time : spatial (EuclideanSpace.single timeAxis (1:ℝ)) = 0 := by
  first
  | (ext i; simp [spatial, Fin.castSucc_ne_last])
  | (ext i; fin_cases i <;> rfl)

theorem time_single_time : time (EuclideanSpace.single timeAxis (1:ℝ)) = 1 := by
  first
  | simp [time]
  | rfl

theorem neg_one_det :
    LinearMap.det ((-1 : (Spacetime →L[ℝ] Spacetime)ˣ).val.toLinearMap) = 1 := by
  have h : ((-1 : (Spacetime →L[ℝ] Spacetime)ˣ).val.toLinearMap) =
      (-1 : ℝ) • LinearMap.id := by
    ext x
    simp
  rw [h, LinearMap.det_smul, LinearMap.det_id]
  first
  | norm_num
  | simp

theorem neg_one_minkowski (x : Spacetime) :
    minkowskiSquare ((-1 : (Spacetime →L[ℝ] Spacetime)ˣ).val x) = minkowskiSquare x := by
  have hx : (-1 : (Spacetime →L[ℝ] Spacetime)ˣ).val x = -x := by simp
  have hs : spatial (-x) = -spatial x := by
    ext i
    simp [spatial]
  have ht : time (-x) = -time x := by simp [time]
  rw [hx, minkowskiSquare, minkowskiSquare, hs, ht, norm_neg, neg_sq]

theorem neg_one_not_orthochronous :
    ¬ (∀ x : Spacetime, (-1 : (Spacetime →L[ℝ] Spacetime)ˣ).val x ∈ forwardCone ↔
      x ∈ forwardCone) := by
  intro h
  have he_mem : (EuclideanSpace.single timeAxis (1:ℝ) : Spacetime) ∈ forwardCone := by
    show ‖spatial (EuclideanSpace.single timeAxis (1:ℝ))‖ ≤
      time (EuclideanSpace.single timeAxis (1:ℝ))
    rw [spatial_single_time, time_single_time, norm_zero]
    exact zero_le_one
  have hneg : ‖spatial ((-1 : (Spacetime →L[ℝ] Spacetime)ˣ).val
        (EuclideanSpace.single timeAxis (1:ℝ)))‖ ≤
      time ((-1 : (Spacetime →L[ℝ] Spacetime)ˣ).val
        (EuclideanSpace.single timeAxis (1:ℝ))) :=
    (h _).2 he_mem
  have h2 : time ((-1 : (Spacetime →L[ℝ] Spacetime)ˣ).val
      (EuclideanSpace.single timeAxis (1:ℝ))) = -1 := by
    simp [time]
  rw [h2] at hneg
  linarith [norm_nonneg (spatial ((-1 : (Spacetime →L[ℝ] Spacetime)ˣ).val
    (EuclideanSpace.single timeAxis (1:ℝ))))]

example : ¬ IsPL (-1 : (Spacetime →L[ℝ] Spacetime)ˣ) :=
  fun h => neg_one_not_orthochronous h.2.2

variable {H : HilbertSpace} {Labels : FieldLabels}

/-! (5) The coordinates pin down the group law of `Symmetry`. -/
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

theorem sym_mul_assoc (P : PoincareAction H Labels) (a b c : P.Symmetry) :
    a * b * c = a * (b * c) := by
  apply coords_ext P
  · simp only [lor_mul, mul_assoc]
  · simp only [tr_mul, lor_mul, Units.val_mul, mul_apply_eq_comp, map_add, add_assoc]

theorem sym_one_mul (P : PoincareAction H Labels) (a : P.Symmetry) : 1 * a = a := by
  apply coords_ext P
  · rw [lor_mul, P.identityCoordinates.1, one_mul]
  · rw [tr_mul, P.identityCoordinates.1, P.identityCoordinates.2, Units.val_one,
      one_apply_eq_self, add_zero]

/-! (6) `translationZero` and `translationAdd` are consequences of the other fields. -/
theorem translationZero_redundant (P : PoincareAction H Labels) :
    P.pureTranslation 0 = 1 :=
  coords_ext P ((P.translationCoordinates 0).1.trans P.identityCoordinates.1.symm)
    ((P.translationCoordinates 0).2.trans P.identityCoordinates.2.symm)

theorem translationAdd_redundant (P : PoincareAction H Labels) (x y : Spacetime) :
    P.pureTranslation (x + y) = P.pureTranslation x * P.pureTranslation y := by
  apply coords_ext P
  · rw [lor_mul, (P.translationCoordinates x).1, (P.translationCoordinates y).1,
      (P.translationCoordinates (x + y)).1, mul_one]
  · rw [tr_mul, (P.translationCoordinates x).1, (P.translationCoordinates x).2,
      (P.translationCoordinates y).2, (P.translationCoordinates (x + y)).2,
      Units.val_one, one_apply_eq_self, add_comm]

/-! (7) Inverses exist in `Symmetry`; hence every `onStates g` is onto (unitary). -/
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

theorem onStates_surjective (P : PoincareAction H Labels) (g : P.Symmetry) :
    Function.Surjective (P.onStates g) := by
  intro ψ
  refine ⟨P.onStates (symInv P g) ψ, ?_⟩
  have h := congrArg (fun T : H.Operator => T ψ) (P.composition g (symInv P g))
  simp only [mul_symInv, P.identity, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at h
  exact h.symm

/-! (8) `onTests` is determined by `pullback`; the identity acts trivially. -/
theorem onTests_unique (P Q : PoincareAction H Labels) (g : P.Symmetry) (g' : Q.Symmetry)
    (h : P.coordinates g = Q.coordinates g') (f : TestFunction) :
    P.onTests g f = Q.onTests g' f := by
  ext x
  rw [P.pullback, Q.pullback, h]

theorem onTests_one (P : PoincareAction H Labels) (f : TestFunction) :
    P.onTests 1 f = f := by
  ext x
  rw [P.pullback, P.identityCoordinates.2, sub_zero, P.identityCoordinates.1, inv_one,
    Units.val_one, one_apply_eq_self]

/-! (9) Given `Faithful`, `W2.labelIdentity` follows from `W2.fieldCovariance`. -/
theorem labelIdentity_of_faithful (T : WightmanTheory H Labels) (hW2 : T.W2)
    (hF : T.fields.Faithful) (ℓ : Labels.carrier) : T.poincare.onLabels 1 ℓ = ℓ := by
  by_contra hne
  obtain ⟨f, hf⟩ := hF _ (sub_ne_zero.mpr hne)
  apply hf
  refine LinearMap.ext fun ψ => ?_
  have hc := hW2.fieldCovariance 1 ℓ f ψ
  have hψ : (⟨T.poincare.onStates 1 ψ.1, hW2.domainInvariant 1 ψ.2⟩ : T.fields.domain) = ψ :=
    Subtype.ext (by
      show T.poincare.onStates 1 ψ.1 = ψ.1
      rw [T.poincare.identity, ContinuousLinearMap.id_apply])
  rw [hψ, onTests_one, T.poincare.identity] at hc
  have key : T.fields.field (T.poincare.onLabels 1 ℓ) f ψ = T.fields.field ℓ f ψ :=
    Subtype.ext hc.symm
  rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, key, sub_self, LinearMap.zero_apply]

/-! (10) Non-vacuity: a `PoincareAction` exists on every Hilbert space and label space
(trivial representation, standard affine pullback via Mathlib's Schwartz composition). -/
def trivialAction (H : HilbertSpace) (Labels : FieldLabels) : PoincareAction H Labels where
  Symmetry := PoincareCoordinates
  one := ⟨(plOne, 0)⟩
  mul := ⟨fun g h => (plMul g.1 h.1, g.1.val.val h.2 + g.2)⟩
  topology := inferInstance
  onStates _ := ContinuousLinearMap.id ℂ _
  onLabels _ := LinearEquiv.refl ℂ _
  onTests g f := SchwartzMap.compSubConstCLM ℂ g.2
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.unitsEquiv ℝ Spacetime g.1.val⁻¹) f)
  pureTranslation x := (plOne, x)
  identity := rfl
  composition _ _ := (ContinuousLinearMap.id_comp _).symm
  unitary _ _ := rfl
  stronglyContinuous _ := continuous_const
  coordinates := Homeomorph.refl _
  identityCoordinates := ⟨rfl, rfl⟩
  productCoordinates _ _ := ⟨rfl, rfl⟩
  translationCoordinates _ := ⟨rfl, rfl⟩
  pullback _ _ _ := rfl
  translationZero := rfl
  translationAdd x y :=
    Prod.ext (Subtype.ext (mul_one (1 : (Spacetime →L[ℝ] Spacetime)ˣ)).symm) (add_comm x y)

example (H : HilbertSpace) (Labels : FieldLabels) : Nonempty (PoincareAction H Labels) :=
  ⟨trivialAction H Labels⟩

#print axioms isPL_inv
#print axioms neg_one_not_orthochronous
#print axioms neg_one_det
#print axioms sym_mul_assoc
#print axioms translationAdd_redundant
#print axioms onStates_surjective
#print axioms labelIdentity_of_faithful
#print axioms trivialAction

end YangMills.AuditPoincare
