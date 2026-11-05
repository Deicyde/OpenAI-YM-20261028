import YM.EveryPhase.Irreducible
import YM.EveryPhase.Implement

/-!
# Reconstruction in each character phase
`Completed` records the Wightman theory, its vacuum, low-energy and heat estimates, irreducibility and the continued stress tensor for each character. Its integration identities recover the unselected correlations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Filter Set MeasureTheory Measure Spec Boundary Next.BOUNDARY OS Stress
open scoped Topology NNReal InnerProductSpace ComplexOrder Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}

/-- Weak commutant using actual unbounded adjoint. (Weak definition with
all field word domain vectors.) This form doesn't need a convention about
what the Lean value of an unbounded operator is off its domain. -/
def member (X : Wightman S) (B : X.operators.H.Op) := ∀ p f (u v : X.operators.domain),
    let T := X.operators.denselyDefined p f
    ∃ (he : u.val ∈ T.adjoint.domain), inner ℂ (T.adjoint (⟨u.val,he⟩)) (B v.val)=
      inner ℂ u.val (B ((X.operators.field p f v).val))

/-- `L` fixes all choices before any arity, test, or point.

In particular
retains the **whole** resolution `F.α.space.Out` and its values on compressed
whole words; no enlargement of the generating algebra.

No further refinement
of the ultraviolet or volume limits used in the Final.

See
`S.Field`, `S.Union`, `Table.useAt`, `Locals` / `Selection.Certificate`
(F.phase), `Maxwell.Ranks` (F.phase.transport.comparator), F.room's CellHyp
and RankWidths, for the common Euclidean part.

So this uses the baseline
spec for Yang-Mills (same gauge quantifiers, schedule/tuning/normalization,
extraction, actual cell copies and corrected detector polynomial root bounds,
ranks etc. as in the old CLOSED).

We include some quantitatives internal to reconstruction because of the
route we take. `zeroE` projection here is PVM (energy 0) on the FULL space,
`bHeat` its boundary evolution e^{-sH}, see `bHeat_pair`, `bHeat_ground`.
Stress: all as Minkowski distributions with spec in Charge/Implement. See
also Tensor for explicit Lorentz conventions and differentiation on labels,
and Decree for the corresponding partial-boundary passage on compact tests,
using the shore data `appointment` in `Force`. Polynomial rule uses arbitrary
representative sections (such sections exist see `Stress.reps`). -/
structure Completed (F : Final C f S) (L : Almanac F) : Prop where
  isTheory (i) : (L.actors i).Realizes (W:=(L.contours i).world) F.sector.turns F.room.kernel.spin
  into_onto (i) : Surjective (L.J i)
  euclid (i) : (L.chambers i).UniqueHeat
  mink (i) (x : (L.actors i).operators.H) : (L.actors i).momentum.region zeroE x=x ↔
    ∃ z : ℂ, z • (L.actors i).operators.vacuum=x
  light (A : SumOfWords S) (h : finite A) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i u, u∈Ioc (0:ℝ) 1 →
    (νletter L i A).real (lowE u) ≤ M*u^2
  heat (A : SumOfWords S) (h : finite A) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ s ≥ (1:ℝ≥0),
    let x := stands (L.actors i).operators A
    let P := (L.actors i).momentum.region zeroE
    let r := inner ℂ x ((bHeat (L.J i) s-P) x)
    0 ≤ r ∧ r ≤ ↑(M*(s:ℝ)⁻¹^2)
  commutant (i) (B) : member (L.actors i) B ↔ ∃ a : ℂ, B=a • ContinuousLinearMap.id ℂ _
  continued_stress (i) : Stress.Force S (F.α.ensemble i) (L.contours i) F.sector.turns F.sector.derivatives
    F.room.kernel.spin (L.actors i) F.sector.energy
  depends (n : ℕ) (v : Fin n → S.Union) (g : Joint n) : Continuous fun i => (L.contours i).world.W n v g
  at_words (v : C.book.Word) (hv : Word.distinct v) : (∫ i,
    (F.α.ensemble i).expect v ∂F.α.space.μ) = S.expect v
  at_boundary (n : ℕ) (v : Fin n → S.Union) (g : Joint n) :
    (∫ i, (L.contours i).world.W n v g ∂F.α.space.μ)=F.B.world.W n v g

variable (F : Final C f S)

theorem all_characters : ∃ L : Almanac F, Completed F L := by
  obtain ⟨L⟩ := almanac F
  exact ⟨L,boundary_realizes L,reaches L,every L,boundary_zero_energy L,light_bound L,inverse_square L,
    fun i B => (precise (L.cores i) B).symm.trans (irreducible L i B),force L,
    fun _ => word_continuity L, F.α.space.barycenter _ F.phase.phase.decomposition
      F.phase.phase.chosen F.room.kernel.translations,fun _ => barycenter L⟩

-- Some unpacked consumer consequences.

open Table in
lemma allPlanes (i : F.α.space.X) (a : Axis) (K : Ortho) (b : E4) :
    ClassWords.tests (F.α.ensemble i) F.sector.turns F.room.kernel.spin a K b :=
  ClassWords.transported _ _ _ _ _ _ (F.phase.phase.states i) F.phase.transport.spots (F.phase.phase.sym i)
    (fun d => (F.phase.phase.retains i d).symm.le)

lemma recognizes {L : Almanac F} (H : Completed F L) (i : F.α.space.X) (d : ℕ) (v : C.book.Ref d) :
    (F.α.ensemble i).vanishes d v ↔ ∀ f : Test4, (L.actors i).operators.field (S.pin d (S.project d v)) f=0 := by
  have ht := F.phase.phase.states i
  have hp : S.project d v = 0 ↔ (F.α.ensemble i).vanishes d v := by
    rw [← (F.α.ensemble i).equivalent ht.smooth ht.laws.toSymmetric,F.phase.phase.retains]; exact Submodule.Quotient.mk_eq_zero _
  rw [← hp]; constructor
  · intro h; simp [h]
  contrapose!; intro h
  exact (H.isTheory i).faithful (S.pin d _) fun hv => h ((S.pin_inj _) (hv.trans (map_zero _).symm))

lemma fixedHeat {L : Almanac F} (H : Completed F L) (i) (x : (L.actors i).operators.H) :
    (∀ s : ℝ≥0, bHeat (L.J i) s x=x) ↔ ∃ z : ℂ, z • (L.actors i).operators.vacuum=x :=
  (bHeat_ground (L.links i) (L.cores i) x).trans (H.mink i x)
lemma exactly_fixed {L : Almanac F} (H : Completed F L) (i) (x : (L.actors i).operators.H) :
    (∀ p, (L.actors i).action.orbit.translation p x = x) ↔ ∃ z : ℂ, z • (L.actors i).operators.vacuum=x := by
  refine ⟨(H.isTheory i).unique x,?_⟩; rintro ⟨z,rfl⟩ p; rw [map_smul]
  exact congrArg (z • ·) ((H.isTheory i).covariance.vacuum (Mink.Poincare.translation p))

end YM.EveryPhase
