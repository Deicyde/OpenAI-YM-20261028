import YM.Push.SECTOR_MEASURE.Bounds

/-!
# Peel a charge in the output formula

Pay under real
Teller Funds. A proposed next-step density estimate must control the
remainder with the **actual multiplier** (`residual` here makes it
particularly clear what gets multiplied). Just writing ANY density this
way doesn't assert any cancellation or usefulness of the resulting RHS;
unpeeling a crown may cost a lot. No interchange of orientation payment
and orbit averaging. E.g. if there are full base rows, channel averaging,
K gas, forced/source terms, this doesn't estimate their difference
from the one fine cut crown. Nor does it deal with already dropped
defaults.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure

open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory
open Next.Fluctuations.Sector
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
  {x W κ : ℝ}

/-- Coarse *cut* crown factor held outside. -/
def shield (T : Tube G S) (β x : ℝ) (V : Config G c) :=
  Real.exp (-β * ∑ i, crown T.down T.low (till x) S.patch.L.val (temp x) V i)

/-- Reciprocal of the operated-on fine cut crown factor. -/
def tear (T : Tube G S) (β x : ℝ) (U : Config G f) :=
  Real.exp (β * ∑ i, crown T.up T.high (till x) 1 (fiery G x S.patch.L) U i)

theorem adjust (U : Config G f) (k : S.Choices) (V : Config G c) (β x : ℝ) :
    taggedKernel S β k U V = shield T β x V * incoming T β x k V U * tear T β x U := by
  unfold incoming
  rw [show shield T β x V * (_ * _ * _) * tear T β x U =
    taggedKernel S β k U V * ((Real.exp (-β * crownGap T x U V) * shield T β x V) * tear T β x U) by
    unfold taggedKernel; ring]
  unfold shield tear crownGap
  rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp





section vectors
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]















end vectors
end YM.Push.SectorMeasure
