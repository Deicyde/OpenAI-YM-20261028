import YM.Push.LOOP_COEFFICIENT.Block.Cruise
import YM.Push.LOOP_COEFFICIENT.OneLoop


/-!
# The smaller remaining vertex port and its interfaces with horizons and scales
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Filter Set Matrix Lattice Laurent Bloch RG Precision Wilson Exterior Tree Bid Complex Portal Fine Vessel Kernel
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {p q : Clip} {H H' : Bed} {P : ChartRatio G} {W : PathData G} {L : Side} {T : Towers L} {V : Vessel G L}
  {ξ u A η e B g σ C D Λ hi δ M K M' F : ℝ}

structure Anchor (G : Gauge) (T : Towers L) (H H' : Bed) (p q : Clip) (ξ u A : ℝ) : Prop where
  deep : T.Deep ξ A 2
  metric : H.metric.strip ξ A
  metric' : H'.metric.strip ξ A
  free n : Floor H p n u A
  free' n : Floor H' q n u A
  sworn n : Sworn H n G
  sworn' n : Sworn H' n G

structure Stream (T : Towers L) (V : Vessel G L) (W : PathData G) (p : Clip) (P : ChartRatio G) (H H' : Bed) where
  coarse : ℕ → Side
  fine : ℕ → Side
  sizes i : (fine i).val = (coarse i).val * L.val
  unbounded : Expands coarse
  S (i : ℕ) : StepData (coarse i) (fine i)
  F i : Forest (S i).ratio
  path i : fieldDir G (coarse i) 1 → AxisChart G (F i)
  charts i (t : (S i).Choices) : V.Charts t (installed (ratioStep sizes i) T.A0) (r:=ratioStep sizes i)
  admits i : Admission (F i) (path i) p W (installed (ratioStep sizes i) T.A0) P
  inputs i : Precision.Inputs (S i) (installed (ratioStep sizes i) T.A0) (H.metric.acts (fine i)) (H'.metric.acts (coarse i))

namespace Anchor
variable (h : Anchor G T H H' p q ξ u A)
include h




end Anchor

structure Synoptic (T : Towers L) (V : Vessel G L) (W : PathData G) (p : Clip) (a : G.ColorIndex) (η F M M' hi δ C : ℝ) : Prop where
  cruise : Cruise V (axisProfile G T.A0) W p η C
  spread : Spread (axisProfile G T.A0) (η/3/2) F
  regular : (loopData W p V T).Regular (η/3) C
  scan : (loopData W p V T).Scan a M M' (η/3) 1 hi δ


end YM.Push.Loops.Block
