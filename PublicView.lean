import PublicTheory
import YM.Fields.System

/-! The public Hilbert space, domain, labels, fields and affine action are the
ones of the supplied reconstruction. There is no second field-system witness. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open MeasureTheory Set Function
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius
variable {G : YM.Gauge} {L : YM.Register G} {S : YM.Table L}
variable (A : YM.Boundary.Wightman S)

def stateSpace : HilbertSpace :=
    { carrier := A.operators.H
      normedAddCommGroup := inferInstance
      innerProductSpace := inferInstance
      completeSpace := inferInstance }

def labelsOf (S : YM.Table L) : FieldLabels :=
    { carrier := S.Union
      addCommGroup := inferInstance
      module := inferInstance }

def fieldsOf : FieldSystem (stateSpace A) (labelsOf S) :=
    { domain := A.operators.domain
      vacuum := A.operators.omega
      field := A.operators.field }

def view : WightmanTheory (stateSpace A) (labelsOf S) :=
  let hilbert := stateSpace A
  let labels := labelsOf S
  let fields := fieldsOf A
  let translations : TranslationAction hilbert :=
    { operator := A.action.orbit.translation
      identity := A.action.orbit.origin
      add := A.action.orbit.sends
      unitary := A.action.orbit.unitary
      stronglyContinuous := A.action.orbit.moves }
  let energyMomentum : EnergyMomentumMeasure hilbert :=
    { projection := A.momentum.region
      empty := A.momentum.none
      univ := A.momentum.all
      intersection := A.momentum.joins
      selfAdjoint := A.momentum.real
      countablyAdditive := A.momentum.unites
      diagonal := A.momentum.diagonal
      finite := A.momentum.finite
      diagonalIdentity := A.momentum.at_pair }
  let poincare : PoincareAction hilbert labels :=
    { Symmetry := YM.Mink.Poincare
      one := inferInstance
      mul := inferInstance
      topology := inferInstance
      onStates := A.action.V
      onLabels := fun transformation ↦
        A.spin.rail transformation.Λ
      onTests := fun transformation ↦
        YM.Boundary.Joint.push transformation
      pureTranslation := YM.Mink.Poincare.translation
      identity := A.action.one
      composition := A.action.mult
      unitary := A.action.usual
      stronglyContinuous := A.action.strong
      coordinates :=
         { toEquiv := { toFun := fun p => (p.Λ, p.b)
                        invFun := fun p => ⟨p.1,p.2⟩
                        left_inv := fun _ => rfl
                        right_inv := fun _ => rfl }
           continuous_toFun := YM.Mink.Poincare.standard.continuous
           continuous_invFun := YM.Mink.Poincare.standard.continuous_iff.mpr continuous_id }
      identityCoordinates := ⟨rfl,rfl⟩
      productCoordinates := fun _ _ => ⟨rfl,rfl⟩
      translationCoordinates := fun _ => ⟨rfl,rfl⟩
      pullback := fun g f x => (YM.Boundary.Joint.push_at ..).trans
         (congrArg f (YM.Mink.Poincare.backwards g x))
      translationZero := rfl
      translationAdd := by
        intro left right
        congr 1
        simp [YM.Mink.Poincare.translation, YM.Mink.Poincare.sends]
        abel }
  let theory : WightmanTheory hilbert labels :=
    { fields := fields
      adjointLabel := A.J
      translations := translations
      energyMomentum := energyMomentum
      poincare := poincare
      translationCompatibility := fun _ ↦ rfl }
  theory

theorem vector_eq (word : List (S.Union × TestFunction)) :
    ((fieldsOf A).vector word).1 = A.operators.vector word := by
  induction word with
  | nil => rfl
  | cons v word ih =>
    simp only [FieldSystem.vector, YM.Boundary.Fields.vector,
      YM.Boundary.Fields.evaluates, YM.Boundary.Fields.edits]
    congr 2
    exact Subtype.ext ih

theorem view_axioms {W : YM.Boundary.Surface S} {V : S.Rotation} {h : S.RealSpin}
    (H : A.Realizes (W := W) V h) : (view A).Axioms := by
  let theory := view A
  let fields := fieldsOf A
  let labels := labelsOf S
  have domainAxioms : fields.DomainAxioms :=
    { normalizedVacuum := H.total.norm
      denseDomain := H.total.everywhere
      cyclicVacuum := by
        change A.operators.domain = _
        rw [H.total.cyclic]
        congr 1
        ext state
        simp only [Set.mem_range]
        constructor
        · rintro ⟨word, rfl⟩
          exact ⟨word, vector_eq A word⟩
        · rintro ⟨word, rfl⟩
          exact ⟨word, (vector_eq A word).symm⟩
      tempered := H.total.temperate }
  have w0 : theory.W0 :=
    { spectralRepresentation := H.spectral
      positiveEnergy := H.forward
      uniqueVacuum := H.unique }
  have w1 : theory.W1 :=
    { domain := domainAxioms
      adjoint := H.adj }
  have w2 : theory.W2 :=
    { labelIdentity := by
        intro label
        exact H.letters.identity label
      labelComposition := by
        intro left right label
        exact H.letters.representation
          left.Λ right.Λ label
      domainInvariant := H.covariance.domain
      vacuumInvariant := H.covariance.vacuum
      fieldCovariance := H.covariance.covariance }
  have w3 : theory.W3 :=
    { locality := H.localPairs }
  exact ⟨w0,w1,w2,w3⟩

theorem publicMoment {W : YM.Boundary.Surface S} (hW : A.operators.realizes W)
    (n : ℕ) (fieldLabels : Fin n → S.Union) (tests : Fin n → TestFunction) :
    (view A).fields.vacuumExpectation fieldLabels tests =
      W.W n fieldLabels (YM.Boundary.Joint.materialize n tests) := by
  let word : List (S.Union × YM.Boundary.Test4) :=
    List.ofFn fun i ↦ (fieldLabels i, tests i)
  change inner ℂ A.operators.vacuum
      ((fieldsOf A).vector word).1 =
    W.W n fieldLabels
      (YM.Boundary.Joint.materialize n tests)
  rw [vector_eq A word]
  have meets := hW word
  unfold YM.Boundary.Surface.expect at meets
  have word_length : word.length = n := by
    simp [word, List.length_ofFn]
  let packed : Σ k, Fin k → S.Union × YM.Boundary.Test4 :=
    ⟨word.length, word.get⟩
  let expected : Σ k, Fin k → S.Union × YM.Boundary.Test4 :=
    ⟨n, fun i ↦ (fieldLabels i, tests i)⟩
  have packed_eq : packed = expected := by
    apply Sigma.ext word_length
    apply (Fin.heq_fun_iff word_length).2
    intro i
    simp [packed, expected, word]
  exact meets.trans (congrArg
    (fun p : Σ k, Fin k → S.Union × YM.Boundary.Test4 ↦
      W.W p.1 (fun i ↦ (p.2 i).1)
        (YM.Boundary.Joint.materialize p.1 fun i ↦ (p.2 i).2))
    packed_eq)

end YangMills
