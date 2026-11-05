import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.Next.EXTRACTION.Base
import YM.Planned.PRIMARY_INTEGRAL_295.Folio
import YM.Push.ABSOLUTE_SUMS.Delay



/-!
# Fixed-L error ceiling and shared entry tasks

These proofs operate on Levels only (not reps); all probabilities &
actual serving/expense outside. Rate optional post-L-realization
for scaled primary path receipts (STAMP denominator `p_m` not period).
Allows every FIXED power in growth. Before promising `Post` on given
schedule must also pay other consumers; this proof does not let these
choices refit with every query.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Thrift
open Function Filter Set Metric Lattice Labels Source RG Wilson Next.Foundations Extra.Histories Bid Warehouse Folio
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {d j t : ℕ}

-- after L thresholds/costs. positive rate to be used for
-- Clock's charges including Other reserves. P powers of suppressed
-- `t`/`g`-terms to absorb further after L if actual estimates.
structure Thunder where
  exponent : ℕ
  level : ℝ
  priced : 0≤level

open Push.AbsoluteSums
open Pressure

abbrev fineMark := Delay.fineMonitor

def storm (V : Thunder) (G : Gauge) (L : Side) (x : ℝ) := V.level * (1+(radiusB x:ℝ))^V.exponent / fineMark G L x






-- Use ratio promise strict >1 for these numerical gates.


/-- Post ceiling at a tuple includes reader's size check (support of the
true principal term additional). Across Levels and all period indices.
No admission conditions on periods promised by the actual localized
step are relaxed. -/
def Pass (K : Levels G) (m d : ℕ) {j t} (D : Supplies j t d) (V : Thunder) (kernel : KernelChoices) :=
   let L:=K.S.block m; let δ:=storm V G L (K.clock.hatBeta m)
   Packing.tol d L δ ≤ 1 ∧ shutter (localSection G d) (sound G d) (valuation G d) D kernel * Packing.tol d L δ ≤ Doors.rate L ∧
   PPX.Blend D.ink.ratio (K.budget (m+1)).threshold (K.budget m).threshold ∧
   Push.Local.hitWidth (K.budget m) * Real.sqrt (K.clock.forcedAllowance m) ≤ 1 ∧ ∀ p, minSide G d ≤ (K.S.side m p).val



abbrev Burst := ℕ → ℕ → ℕ → Thunder
open Folio Warehouse

/-- Quantifiers: all OK certificates across same/j-1 boundaries,
ALL d. Pass at uniform entrance BEFORE periods but POST allocation of
lengths and polynomial power/constants. Here use of one common x via
fixed βf/profile. -/
def Books (K : Levels G) (P : ℕ → Stage) (I : Library) (V : Burst) :=
  ∀ m d (h : Okay P (K.clock.J (m+1)) (K.clock.J m) d),
    Pass K m d (shoes G I h) (V (K.clock.J (m+1)) (K.clock.J m) d) K.clock.kernel


end YM.Planned.PrimaryIntegral295.Thrift
