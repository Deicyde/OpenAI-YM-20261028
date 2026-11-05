import YM.Push.FREE_RESOLVENT.AlignProbe
import YM.Push.FREE_RESOLVENT.Atlas
import YM.Work.C04

/-!
# Align the Gram matrices AFTER path-length cutting

Shared gauges at both periods handled separately by the active injection;
no free interior stationarity assumptions. This component only uses
Branches and field inputs on matching local sites (via actual perturbation
maps). Sum neighborhood is for actual coordinates. The margins here are
*tests on the schedule*, not consequences assumed of infinite periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine.View
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open Work.F08 Lifted Mark Work.E03
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f f' c c' n : Side} {S : StepData c f} {P : Patch} {K : KernelChoices}
variable {R r : ℕ} {s : Signed} {o : Site c} {o' : Site c'}
variable {h : f.val=c.val*P.L.val} {h' : f'.val=c'.val*P.L.val}






-- Compare just positions (plaquette type separately tested).




section lines
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {u : X →L[ℝ] Vec G c 1} {u' : X →L[ℝ] Vec G c' 1} {m : ℕ}



omit [NormedSpace ℝ X] in
lemma runs {Y : Type*} [TopologicalSpace Y] {w : X → Y} {ι κ : Type*} {F : Y → Matrix ι κ ℝ}
    {a : ι → Site c} {b : κ → Site c} {R} {t x}
    (h : Lives a b R F t) (hw : Tendsto w (𝓝 x) (𝓝 t)) : Lives a b R (F ∘ w) x :=
  fun i j hg => hw.eventually (h i j hg)

def floorMark (P : Patch) (r : ℕ) := View.reach P+r+16

def lengthMark (P : Patch) (r m : ℕ) := m+10*(floorMark P r)




end lines
end YM.FreeResolvent.Affine.View
