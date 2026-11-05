import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.Tannery
import YM.Analysis.Symmetric
import YM.Bid.Station


set_option warningAsError false

/-!
# Passing the class symmetries through stationarity. True root, tags and
physical periods. `torch` projects the physical transformed representative,
not a new independently chosen scene. Works even when the signed group
moves the tree.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Tent
open Lattice RG Exterior Wilson Precision Tree Bid 
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {B : Forest S.ratio} {p : Clip} {W : PathData G} {σ T C g : ℝ} {r : Dir G c→AxisChart G B}
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]




def lived (p : Clip) (W : PathData G) {t : S.Choices} (B : Forest S.ratio) (r : Dir G c→AxisChart G B) (a : Dir G c) := tested B t p W a (r a)

section params
variable (h : Larger (G:=G) S) (hW : W.Bounds p σ T C) (hB : Critical B p W r) (hp : PriceGap B p W g) (hg : 0<g) (t : S.Choices)
include h hW hB hp hg


omit h hW hp hg in
lemma lives : ContDiffAt ℝ ω (lived p W B r (t:=t)) 0:= by
  let P : Dir G c→ _ :=fun x => (x,r x)
  have he : P 0=0:=by simp [P,hB.1]
  exact ContDiffAt.comp (f:=P) (g:=uncurry (tested B t p W)) 0 (he.symm ▸ (hB.2.2 t).1) (contDiffAt_id.prodMk hB.2.1)


end params
end YM.Progress.ClassicalKin.Tent
