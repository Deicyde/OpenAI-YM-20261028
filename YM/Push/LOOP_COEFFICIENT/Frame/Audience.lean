import YM.Push.LOOP_COEFFICIENT.Block.Optimize

/-!
# Reading centered and rooted group expressions on arbitrary periods before differentiating
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Frames
open Function Matrix Set Filter Lattice Laurent RG Precision Exterior Wilson Pressure Complex Gauge Block
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {M : Matrix (Body 1 f) (Body 1 c) ℝ}

abbrev Native (G : Gauge) (c f : Side) := Loops.Links G c × Dual G c f















variable (h : S.patch.Branches S.kernel G)
include h



end YM.Push.Loops.Frames
