import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.ODE.ExistUnique
import YM.Next.MAXWELL.System

/-!
# Rank also with genuine Shot rows

Useful on the comparator side of RShort (before smooth physical limits).
Only the free side. Pair smears, square detector on complementary classes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick Dash
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder Matrix
variable {G : Gauge} (F : Labels.Frames G) (d : ℕ)
lemma live : Live (Model F) := fun _ _ f => Test.smearing f ((Model F).smooth_read (table_smooth F) _).continuousOn







end YM.Maxwell.Free
