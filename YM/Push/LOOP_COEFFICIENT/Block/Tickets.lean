import YM.Push.LOOP_COEFFICIENT.Block.Spire

/-!
# District-scale prices
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Matrix Function Filter Set Lattice Laurent Bloch RG Precision Exterior Complex Wilson Fine Portal
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {L : Side} {a d : Type} [Fintype a] [DecidableEq a] [Fintype d] {η e σ C A B g : ℝ}
abbrev ground (G : Gauge) (L : Side) := lower L (Axes G)

abbrev lobby (G : Gauge) (L : Side) := versor L G.ColorIndex
variable {X : Vertex d (Co L a) (Co L a)}












structure Machine (T : Lights G L) (W : PathData G) (p : Clip) (η B : ℝ) : Prop where
  local_cost : Charge (ground G L).dual (ground G L) (slab T W p) η B
  mill_cost : Charge (lobby G L) (ground G L) (mill T) η B
  ash_cost : Charge (ground G L).dual (ground G L) (ash T) η B
  ash_rare : Pay (ground G L).dual (ground G L) (ash T) η B
  tail_cost : Charge (lobby G L) (lobby G L) ((worm T).pow depth) η B
  tail_rare : Pay (lobby G L) (lobby G L) ((worm T).pow depth) η B


end YM.Push.Loops.Block
