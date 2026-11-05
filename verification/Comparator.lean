import YM
import YM.Examples.SU2
import Lean
set_option autoImplicit false

open YM

universe u v

/-- The checked public signature has only the stated gauge and penalty inputs. -/
example (G : Gauge) (hG : G.Simple) (b : ℝ) (hb : 0 < b) :
    Nonperturbative.Headline.WilsonExistence.{u,v} G hG b :=
  Nonperturbative.existence G hG b hb

/-- The original Wilson existence requirement follows from this same result. -/
example : Spec.CLOSED := by
  intro G hG
  obtain ⟨C,_,_,orders⟩ := Nonperturbative.existence.{0,0} G hG 1 zero_lt_one
  obtain ⟨q,S,F,_⟩ := orders Extraction.Order.full
  exact ⟨C,Extraction.Order.full.refine q,S,⟨F⟩⟩

/-- The defining SU(2) example supplies the simplicity proof and a positive penalty. -/
example : Nonperturbative.Headline.WilsonExistence.{0,0} Next.Foundations.SUtwo Examples.SU2.simple 1 :=
  Examples.SU2.existence

open Lean Elab Command in
run_cmd do
  for name in [`YM.Examples.SU2.simple, `YM.Examples.SU2.existence] do
    let axioms ← collectAxioms name
    unless axioms.all ([`propext, `Classical.choice, `Quot.sound] : List Name).contains do
      throwError "Unexpected axioms for {name}: {axioms}"
    logInfo m!"{name} axioms: {axioms}"
  logInfo "SU2_CHECK_PASS"

run_cmd Lean.logInfo "COMPARATOR_PASS"
