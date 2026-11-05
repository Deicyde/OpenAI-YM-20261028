import YM.RG.History


set_option warningAsError false
/-!
# Lifting a coarse plot through the ACTUAL conditional probability kernel

Work at finite N,p. Constants in envelopes can depend on them and step data.
Except: the sup-bound for *accept*, the conditional-average direction,
preserves the input bound exactly. No other cutoff-uniform estimates claimed
here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror
open Set Filter Function MeasureTheory RG Wilson Lattice
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

abbrev SmallQ {E : Type*} [MeasurableSpace E] (F : E → ℂ) := Envelope F
namespace SmallQ
variable {E D : Type*} [MeasurableSpace E] [MeasurableSpace D] {F H : E → ℂ}











end SmallQ

namespace Block
variable {c f : Side} (S : StepData c f) (β : ℝ) (F : Config G c → ℂ)

/-- No volume factor and no vacuum density inserted in this averaging
DIRECTION. Do not confuse with `StepData.push`. -/
def accept (U : Config G f) :=
    ∫ V : Config G c, (S.density β U V : ℂ)*F V ∂prior G c

section
variable {S β F} (H : S.IsKernel β G)
include H








variable {X : Config G f → ℂ}



end








end Block
end YM.ProjectorNext.RMirror
