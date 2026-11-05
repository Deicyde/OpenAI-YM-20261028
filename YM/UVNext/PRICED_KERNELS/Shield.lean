import YM.Next.SCHEDULE.Layers
import YM.Push.PRICE_COMPILER.Authors
import YM.UVNext.PRICED_KERNELS.Echo



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Extension of local residue for costing only

Restore actual derivative equality on link arrays by a SEPARATE small-field
hypothesis on a single plaquette evaluation. This is not asserting equality of
jets at the boundary of every mask nor an analytic extension outside the Lie chart!
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG RG.Supply Wilson Precision Exterior Gauge Work.G07
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}
section germs
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [HasContDiffBump E]


-- not closedBall_mem_nhds args, eventually beta
lemma advance_local (U : Config G n) (A : Directions G n) : Tendsto (fun t : ℝ => increment U (t • A)) (𝓝 0) (𝓝 U) := by
  have h : Continuous fun t : ℝ => increment U (t • A) := continuous_pi fun i => by unfold increment; fun_prop
  simpa only [zero_smul,at_zero_increment] using h.tendsto (0:ℝ)
omit [HasContDiffBump E] in
theorem left_congr {f g : Config G n → E} {U : Config G n} (h : f =ᶠ[𝓝 U] g) (l : List (Directions G n)) :
    leftDerivs f l =ᶠ[𝓝 U] leftDerivs g l := by
  induction l with
  | nil => exact h
  | cons A l IH =>
    -- nbhd where they agree as germs
    filter_upwards [eventually_eventually_nhds.mpr IH] with i hi
    have he : (leftDerivs f l ∘ fun t : ℝ => increment i (t • A)) =ᶠ[𝓝 0] _ := (show (leftDerivs f l ∘ fun t : ℝ => increment i (t • A)) =ᶠ[𝓝 0] (leftDerivs g l ∘ fun t : ℝ => increment i (t • A)) from (advance_local i A).eventually hi)
    exact he.deriv_eq
end germs

section site
variable (G : Gauge)










end site
end YM.UVNext.PricedKernels
