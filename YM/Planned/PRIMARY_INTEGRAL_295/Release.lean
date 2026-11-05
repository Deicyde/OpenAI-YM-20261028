import YM.Planned.PRIMARY_INTEGRAL_295.Thrift

/-!
# Across all reference levels and periods. Receipt-facing producer

Use certified trigger price envelopes from *sheet & Burst*, not selected
cases. `Credentials` external physics debts: same H's Stamp analytic
& local account and two real Atom input bills. References here can be
any tail as long as gowns stage OK (Doors). Does not assert that physical
producers/resources always available!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Release
open Function Filter Set Lattice Labels Source RG Wilson Next.Foundations Extra.Histories Bid Warehouse Folio Thrift
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} (H : History G)

abbrev now (H : History G) (m : ℕ) := H.levels.clock.J m
abbrev admiss (g : ℕ → Stage) (m d : ℕ) := Okay g (now H (m+1)) (now H m) d





-- simultaneous stage release.
structure Crew (C : ℕ→ℝ) (g : ℕ→Stage) (I : Library) (U : Burst) (r : ℕ→ℕ) : Prop where
  tuned : H.levels.clock.stage=g
  sizes : ∀ m d : ℕ, r d ≤ m → admiss H g m d
  buys : Buy G I H.levels.clock.kernel g C
  ready : Books H.levels g I U



-- export witnesses explicit heading via Lane.Pre



end YM.Planned.PrimaryIntegral295.Release
