import YM.Extra.FREE_DETECTOR_ALGEBRA.Forest

set_option warningAsError false

/-! Laurent-type coefficient extraction for finite Ward tests.
`mood`: a genuine punctured real germ, no distribution at the center.
Only extracting *one* coefficient at a time. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.Residue
open Function Filter Set Tensor Analysis Maxwell Wick Pair
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

def grade (g : ℝ→ℂ) (j : ℕ) := ((j.factorial:ℝ)⁻¹) • iteratedDeriv j g 0



@[simp] lemma grade_zero (g : ℝ→ℂ) : grade g 0=g 0 := by simp [grade]











variable {f g : ℝ→ℂ} {j k v : ℕ} {c b : ℂ}


















end YM.Extra.FD.Residue
