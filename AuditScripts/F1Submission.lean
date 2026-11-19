import Construction
import Audit.Repair.F1

/-! Audit check (not part of the submission): the submission's construction satisfies repair F1.

`EveryPhase.Completed F L` gives, at every character `i`, a Wightman theory `L.actors i` that
realizes the world of the contour `L.contours i`, and the almanac's card `L.cards i` says that this
contour continues the phase `i` (`fromPhase`). `perCharacter_of_completed` reads these data as
`publicReconstruction` (HierarchyBridge.lean) reads the selected phase's, and
`submission_satisfies_F1` follows from `constructed` as `Solution.lean` derives `jointExistence`.
It needs the compiled submission: run with `lake env lean AuditScripts/F1Submission.lean`. -/

set_option autoImplicit false
noncomputable section

namespace YMAudit.F1
open YangMills YM YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary
open Function Set MeasureTheory Filter
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius NNReal

variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- Every character of the submission's hierarchy has reconstruction data. -/
theorem perCharacter_of_completed (L : EveryPhase.Almanac F) (h : EveryPhase.Completed F L) :
    PerCharacter (hierarchy F Q) := fun i => ⟨{
  H := stateSpace (L.actors i)
  theory := view (L.actors i)
  continuation := fun v z x => (L.contours i).waves.F _ z x (fun k => S.pin (v k).1 (v k).2)
  axioms := view_axioms _ (h.isTheory i)
  faithful := (h.isTheory i).faithful
  acts := by
    let a : S.Tag := ⟨0, S.unit 0⟩
    have ne : S.pin 0 (S.unit 0) ≠ 0 := fun e =>
      S.alive 0 F.room.kernel.laws ((S.pin_inj 0) (e.trans (map_zero _).symm))
    obtain ⟨f, hf⟩ := (h.isTheory i).faithful _ ne
    exact ⟨a, f, hf⟩
  analytic := by
    intro n v x
    exact (L.cards i).fromPhase.heat.hol n _ x
  root := by
    intro n a x hx
    have eqx :
        YM.Boundary.place (Hierarchy.spatialPoints x) (fun k => YangMills.time (x k)) = x := by
      apply PiLp.ext
      intro k
      exact YM.position_eta (x k)
    have root := (L.cards i).fromPhase.heat.roots n a (Hierarchy.spatialPoints x)
      (fun k => YangMills.time (x k)) hx
    rw [eqx] at root
    exact root
  boundary := by
    intro n a hgt hh tests
    have edge := (L.cards i).fromPhase.emerges.profile n
      (fun k => S.pin (a k).1 (a k).2) hgt hh (YM.Boundary.Joint.materialize n tests)
    change Tendsto _ _ (𝓝 ((view (L.actors i)).fields.vacuumExpectation _ tests))
    rw [publicMoment _ (h.isTheory i).meets]
    have eqShift (r : ℝ) (x : YangMills.Points n) :
        Hierarchy.complexShift r hgt x = YM.Boundary.shift x (r • hgt) := by
      funext k
      simp [Hierarchy.complexShift, YM.Boundary.shift, Pi.smul_apply, YangMills.time, YM.time]
    have eqSpace (x : YangMills.Points n) : Hierarchy.spatialPoints x = YM.Boundary.trace x := rfl
    simp only [hierarchy, Hierarchy.tensorTest, eqShift, eqSpace,
      YM.Boundary.Waves.atSlopes, YM.Boundary.Waves.restricted,
      YM.Boundary.Joint.material_at] at edge ⊢
    exact edge }⟩

/-- The submission proves `JointExistence` with repair F1. -/
theorem submission_satisfies_F1 : JointExistenceF1 := by
  intro g hg
  obtain ⟨C, _, _, reg, orders⟩ := YangMills.constructed.{0,0} g hg 1 zero_lt_one
  refine ⟨YangMills.wilsonFamily C, reg, fun p hp => ?_⟩
  let a : YM.Extraction.Order := ⟨.full, ⟨p, hp⟩⟩
  obtain ⟨q, S, F, L, Q, M, X, core, -, -, -, -, indep, -⟩ := orders a
  exact ⟨q.per, q.per.monotone, YangMills.hierarchy F Q, core,
    perCharacter_of_completed F Q L indep.reconstruction⟩

end YMAudit.F1

#print axioms YMAudit.F1.perCharacter_of_completed
#print axioms YMAudit.F1.submission_satisfies_F1
