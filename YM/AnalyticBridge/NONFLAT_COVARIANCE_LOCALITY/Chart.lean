import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Motion



/-!
# Real-coordinate sector germs

Full coarse directions, noncommuting matrix coordinates. Replica crossings and
all rotated reads made at the actual input field. No smoothness of geometry
indicators. This is an extension of D's formula with `A` held fixed. Do not
infer that A still records the flags of the varied field, nor differentiate
those flags. Use **ordinary** ordered chart partials (`jet` of
`YM.Push.FREE_RESOLVENT`). Not the invariant Lie-derivative list.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality
open Lattice RG Wilson Pressure Precision Tree 
open Next.SectorChange Next.SectorChange.Motion
open Function Metric Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

/-- Scalar real coordinates on *every* physical, positive coarse bond. `Prices`
of SC uses the Lie color frame (including normalization), sup norm here. -/
abbrev Coord (G : Gauge) (c : Side) := Prices G (Bond c)

abbrev Index (G : Gauge) (c : Side) := Bond c × G.ColorIndex



variable {G : Gauge} {c f : Side}

abbrev root (i : Index G c) : Site c := i.1.1

def coarse (V : Config G c) (z : Coord G c) := RG.increment V (tape z)

lemma coarse_zero (V : Config G c) : coarse V 0=V := by
  rw [coarse, show tape (0 : Coord G c)=(0 : Directions G c) from gaugeCount.map_zero]
  exact increment_zero ..



























end YM.AnalyticBridge.NonflatCovarianceLocality
