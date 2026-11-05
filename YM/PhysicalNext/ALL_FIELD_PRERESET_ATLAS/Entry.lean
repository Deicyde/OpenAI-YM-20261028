import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Prices

/-!
# Input alphabet of the gas at an output site set

This is **not** the alphabet that will appear in `Collection.earlyValue`. It is the
component alphabet before taking the logarithm and restoring exclusions, and with just
the output **base** action (not the complete canonical prescription) taken out.
`Palette` is small notation for the relevant *traces* (family, not quotient by
support or by evaluation). In applications these traces come from the physical Roster
spelling, not from fitting an evaluation. See `Negative` and `OriginalLight` below
for the two different size/regularity uses and the physical assembler for how they are
tied to actual functions. .
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas
open RG Lattice Wilson MeasureTheory Push.AbsoluteSums Push.LogIdentity
open scoped Matrix.Norms.Frobenius ContDiff Classical BigOperators Topology

abbrev SheetFunction (G : Gauge) (n : Side) := Config G n → ℝ

/-- Complete supports. `X` for first-unforced letters, forced entries with their true
inventory for first-forced letters. This is at the fixed output (final flag-read
convention); in particular do *not* use these supports in an integration of those
output flags. The generator must supply complete dependencies, not start from a
smaller core support and infer absence of answers outside it from values that happen to
agree. -/
structure Pane (G : Gauge) (n : Side) (ι κ : Type) where
  X : ι → Support n
  full i : (X i).Nonempty
  forces : κ → ForcedAddress G n

/-- No nonvanishing test used to enumerate an address. `u` before masking includes its
extension, `d` already includes every test. -/
structure Palette (G : Gauge) (n : Side) (ι κ : Type) where
  u : ι → SheetFunction G n
  d : κ → SheetFunction G n

variable {G : Gauge} {n : Side} {ι κ : Type}
namespace Pane

variable (M : Pane G n ι κ)

abbrev Y (i : κ) := (M.forces i).support
abbrev I (i : κ) := (M.forces i).inventory

lemma inside (i : κ) : M.I i ⊆ M.Y i := (M.forces i).inventory_sup
lemma realZone (i : κ) : (M.Y i).Nonempty := (M.forces i).inventory_ne.mono (M.inside i)

/-- The first-system terms, NOT the logarithm. Exact coverage, even at flags and at
hard indicator equality. -/
def initial (p : BudgetPoint) (F : Palette G n ι κ) (V : Config G n) : Finset (κ ⊕ ι) → ℝ :=
    let Q := flags p.threshold V
    gasTerm (both M.Y M.X) (onlyL M.I) Q (Sum.elim (fun i => F.d i V)
      (Restore.good M.X Q fun i => F.u i V))

end Pane

/-- Local-function clause. Even for `d`, the test and every argument still have support
requirements. Not the whole-motion/size or symmetry clause. The smoothness here is on
`Healthy`, and is for `u` *before* masking. -/
structure OriginalLight (p : BudgetPoint) (M : Pane G n ι κ) (F : Palette G n ι κ) : Prop where
  unmasked i : p.Regular (M.X i) (F.u i)
  hardReads i : UsesFinal p.threshold (M.Y i) (F.d i)
  testReads i : UsesFinal p.threshold (M.Y i) (M.forces i).extraTest
  hardMeas i : Measurable (F.d i)
  testMeas i : MeasurableSet {V | (M.forces i).extraTest V}
  hardGauge i : GaugeInvariant (F.d i)
  testGauge i (k : Site n → G.El) (V : Config G n) :
    (M.forces i).extraTest (Lattice.gauge k V) ↔ (M.forces i).extraTest V
  proper i V : F.d i V ≠ 0 → (M.forces i).eligible p.threshold V

/-- Size proof inputs *on component charges*, no charge on assembled clusters here. The
last height isn't required small for the first-exact use. `grade` not to be equated
automatically to a charge needed after the masks move. -/
structure BidLog (ι κ : Type) where
  soft : ι → ℝ
  hard : κ → ℝ
  grade : ℝ
  gamma : ℝ
  margin : ℝ
  factor : ℝ
  top : ℝ

namespace BidLog
variable (b : BidLog ι κ)

structure Offers (p : BudgetPoint) (M : Pane G n ι κ) : Prop where
  grade : 0 ≤ b.grade
  ready : Trees.Ready M.X p.B b.soft b.grade b.gamma b.margin b.factor
  hard i : 0 ≤ b.hard i
  hit : Ac.Hit M.Y p.B b.hard b.grade b.top

variable {p : BudgetPoint} {M : Pane G n ι κ}

lemma absolute (hb : b.Offers p M) : Summable b.soft ∧ Summable b.hard :=
  ⟨(Price.priced_total _ _ hb.ready.2.2.2.2.1
      (by linarith [hb.grade,hb.ready.2.1]) hb.ready.2.2.2.2.2 M.full).2.1,
    (Price.priced_total _ _ hb.hard hb.grade hb.hit M.realZone).2.1⟩

/-- Numerical bounds actually paid BEFORE the second log. Derived from the real
letter income in the physical invocation. -/
structure Negative (p : BudgetPoint) (M : Pane G n ι κ) (F : Palette G n ι κ) : Prop where
  offers : b.Offers p M
  soft i V : Healthy p.threshold (M.X i) V → ‖F.u i V‖ ≤ b.soft i
  hard i V : ‖F.d i V‖ ≤ b.hard i

end BidLog
end YM.PhysicalNext.PreAtlas
