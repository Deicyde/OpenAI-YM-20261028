import YM.Push.STRESS_FLUX.Polynomial


/-!
Physical stress insertions.

The actual cylinders next to the stress shell are **not**
prescribed as e.g. a single clover formula.

Translation is of
the cutoff expression itself even at varying offsets. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Lattice Wilson RG Labels Source Function Set Filter Gauge MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} (C : Family G)

def token (w : Coeff) (a b : Axis) : C.label 4 := (C.labels.level 4).coords (stress G w a b)

def physical (w : Coeff) (N p : ℕ) (x : Site (C.side N p)) (U : Config G (C.side N p)) (a b : Axis) :=
    C.O N p (d:=4) (token C w a b) x U










def weight (t : ℝ) (w : Coeff) : Coeff := fun i => if i=0 then w i else t^2 * w i






open Next.Foundations

end YM.StressFlux
