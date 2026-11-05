import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.Planned.ATOM_REGULAR_ESTIMATE.Bills
import YM.Push.LOCAL_SPLITTING.Funding


/-! Numeric entrance gates for the L^-(d+1) term and the priced large-support
tail. Explicit pre (ratio) versus post (needs later actual thresholds at given
ratio). These are proof-independent passage prices at the AtomStep NORMS,
not global existence of calendars, not claiming analytic receipts can be met. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Rates
open Function Filter Lattice Wilson RG Source Labels Push.Local Extra.Histories Doors
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {d k : ℕ} {F : Labels.Frame G d}



/-- Stage pair `u` incoming, `v` receiving. The latter pays turn/credits. -/
structure Before (A : Hol G) (T : SectionData F) (r : ℕ) (u v : Stage) (C w : ℝ) (L : Side) : Prop where
  large : 4≤L.val
  trade : 20*phaseBase r v.supportExponent ≤ (L.val:ℝ)*u.supportExponent
  main : Motion.orbitCost F*readPrice A F * headBill G L v.order d r C u.supportExponent v.supportExponent < rate L
  rem : turnCost v.order v.power*(2*factor A T v.supportExponent w) * headBill G L v.order d r C u.supportExponent v.supportExponent < rate L




end YM.Planned.AtomRegular.Rates
