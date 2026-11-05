import YM.Progress.CLASSICAL_KIN_RECURSION.Customs

set_option warningAsError false

/-!
# Joint fine/coarse SITE-frame functional

Center is the true matrix-projected weighted center of the minimizing
frames, per physical site. Functions off neighborhoods also given by these
defs; DON'T need estimates of power series denominators there. On origin
germs pull back to exact analytic chart. No independent atom tags. Hessian
to be identified in Screen.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Tent
open Lattice RG Exterior Wilson Precision Tree Bid 
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {B : Forest S.ratio} {p : Clip} {W : PathData G} {σ T C g : ℝ} {r : Dir G c→AxisChart G B}
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

abbrev Frame (G : Gauge) (n : Side) := fieldDir G n 0
abbrev Hall (G : Gauge) (c f : Side) := Dir G f × Frame G c
abbrev Tower (G : Gauge) (c f : Side) := Dir G c × Hall G c f












section analytic
variable (h : Larger (G:=G) S)
include h

omit h in
lemma focus_one : G.focus 1=1:= (mem_of_mem_nhds G.nearest_is_focus 1 (fun i=>by simp)).symm

















end analytic
end YM.Progress.ClassicalKin.Tent
