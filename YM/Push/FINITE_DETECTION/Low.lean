import Mathlib.Analysis.Calculus.TaylorIntegral
import YM.Push.FINITE_DETECTION.NoLinear


/-! Actual finite detector on any `Makes` family and projector below weight four. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection
open Function Filter Set MeasureTheory Dash Extraction Next.Extract
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {d : ℕ}






lemma ref_low (h : G.Simple) (hd : d < 4) (v : C.label d) : ∃ a : ℂ, v = a • C.refUnit d := by
  let F := C.labels.level d
  obtain ⟨c,hc⟩ := Low.labels_low h hd (F.coords.symm v)
  let r := ((C.S.a (C.ref d):ℂ)^d)
  have hr : r ≠ 0 := pow_ne_zero _ (by exact_mod_cast (C.S.a_pos (C.ref d)).ne')
  refine ⟨c/r,?_⟩
  change v = (c/r) • r • F.e0
  rw [smul_smul, div_mul_cancel₀ _ hr, ← F.coords_unit, ← map_smul,← hc,F.coords.apply_symm_apply]


end YM.Push.FiniteDetection
