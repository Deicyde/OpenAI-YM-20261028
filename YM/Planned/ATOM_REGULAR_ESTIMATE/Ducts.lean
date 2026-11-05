import YM.Extra.SOURCE_HISTORIES.Pencil
import YM.Next.SCHEDULE.Clocks
import YM.Next.SCHEDULE.Layers
import YM.Planned.ATOM_REGULAR_ESTIMATE.Sampled
import YM.Planned.ATOM_REGULAR_ESTIMATE.Vest


/-!
Make the *post-length* payments for the `propelled` route, on any p of
this actual realization. This is gauge-local arc pricing in operator sup.
Especially an arbitrarily shaped torus cannot be evaluated on an input
panel of growing unrestricted sup then quoted here with that volume factor
swept into a pre-L constant. The estimate applies e.g. to extended *patch*
inputs with the bounds in this file. That still needs the Covers producer
for genuine marker insertions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Foliage
open Function Set Metric Filter RG Wilson Precision Lattice Tree Pressure Bid Push Uniform Next.Foundations
open WardBin.Lies Short Sample Collar Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical




variable {G : Gauge} {K k : ℕ} {j : ℕ} {Q : KernelChoices}
section Cash
open Clock

def ether (x : ℝ) := gap x * watch 2 x

lemma vapors (k : ℕ) (U : ℝ) : Tendsto (fun x : ℝ => U*ether x * (1+(Clock.cover x:ℝ))^k) atTop (𝓝 0) := by
  have hx := (((ceiling_cheaper 2 1 k one_lt_two zero_lt_one).mul (light 2 ((2:ℕ):ℝ) 1 (by norm_num))).const_mul U)
  simp only [mul_zero,Real.rpow_natCast,Real.rpow_one] at hx
  refine hx.congr' ?_; filter_upwards with x; have hp : watch 2 x > 0 := wp 2 x
  unfold ether; field_simp



end Cash
end YM.Planned.AtomRegular.Foliage
