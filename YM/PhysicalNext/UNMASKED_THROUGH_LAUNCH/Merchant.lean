import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.WILSON_STARTUP.Builder
import YM.Further.STRONG_STARTUP_CREDIT.Launch
import YM.Next.WARD_BIN.LabelEst
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Dome
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.STRESS_FLUX.Matching
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Handoff
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free


/-!
# Purchasing One Horizon / Kin / Steps setup. Pledge

Preserve `s.profile` when setting final floorL after quote. Arbitrary
larger floors & any corresponding Rolls; eta set before post; quantifies
over arbitrary post prices subject to the guards there, picks post-L
parameters and can still take ANY Boost for issuance of Wait/Levels. Does
not assert these suffice for all subsequent purposes. Earns huge
non-conditional readiness for this `a` (TopPath), incl regularized Wilson
input paths that work as `B70 Kin`, arc/loop and path prices through that
Kin's history of metrics, and pre-L geometry-compatible chart/O. Also some
startup, marked, Sector calculation allowances on `a`. Does NOT prove
that `Directed.Program` holds with these purchases, for *any* choice. See
Use and SERVICE for two applications (recipes actually selected).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.ThroughLaunch
open Function Filter Lattice RG Source Wilson Precision RG.Supply Input
open WilsonStartup Further.StrongStartup Extra.Histories Next.Foundations Pressure Testing Org
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

abbrev raise (s : Sheet G) (n : ℕ→ℕ) : Sheet G := {s with floorL:=n}



variable {s : Sheet G} {T : MapPrices} {n : ℕ → ℕ} {L : Rolls (raise s n)} {Θ : Protection L} {D : Delays Θ}
    {Q : PostCost L} {Y : Bar D} {W : Wait Y}

/-- Freeze the data on this output-calibration, witnesses for ALL history lengths and periods,
M is the post-facing kinetic choice (supplies actual unmasked station/path Hessian & alpha receipts,
higher-order shape etc. as in Kin.Planned). No awaiting a choice of cheap L in which
only kinetic penalties isolated are paid. `layer` recovers the earlier free and
thermal purchases for M (not for another orientation). -/
structure TopPath {s : Sheet G} {n : ℕ → ℕ} {L : Rolls (raise s n)}
    (O T : MapPrices) (l : ℕ → ℝ) (Q : PostCost L)
    (a : Levels G) (M : Horizon a) (k : Kin M (chart G)) : Prop where
  finalMap : M.Suffices (Builder.quote s T)
  paths : k.Planned Q
  top i : k.path i i = Design.top G (a.params i).clip
  layer : ∃ (X W : Horizon a) (u : Kin W (chart G)), Craft.Rack a O X ∧ Next.Free.Present a X l ∧
    Bid.Retained W X ∧ W.Suffices T ∧ Next.Free.Present a W l ∧ (∀ N m t, m ≤ N → Bid.Sworn (W.H N m) t G) ∧
      Stationary.FullPaths u Q ∧ k.path=Change.revised u ∧ k.alpha=u.alpha ∧
      (∀ N m p F, m+1 < N → k.stationary N m p F = u.stationary N m p F) ∧ Change.Overlay M W

open Next.Scheduling Next.SectorChange

-- PAY even if scheduling grows after this. These requirements available
-- on the j-height, not taken from a finally-chosen realization.



/-- Pre knobs P chosen such that any higher AFTER floors/numbers called
below work. Pay on the actual input of a given StepData in the Typed
context. `O` here is the initial rack price, `T` the next from Free; no
renaming P to query in nonlinear inputs after applying Builder's quote
(this would be dependent on a later number). Epoch floor statuses are
synchronizable by choosing larger floors **before** Hull analysis.
-/
structure Pledge (s : Sheet G) (O T : MapPrices) (l γ C : ℕ → ℝ) (p : Bid.Worth)
    (t : Tariffs) (B : Extra.Multi.Scope) (v : ℕ → ℕ) : Prop where
  slopePrice i : 0<γ i
  suitable i : s.first ≤ i → Design.Suitable G (s.profile i)
  liftL : s.floorL ≤ v
  plan : Doors.Plans s C p
  -- θ thresholds imposed later; shell growth can still be enlarged there
  ship (n : ℕ→ℕ) (hn : v ≤ n) (L : Rolls (raise s n)) :
    ∃ η : ℕ→ℝ, Stationary.BudgetGap (raise s n) L O η ∧
    ∀ Q : PostCost L, Q.η=η → 1 ≤ Q.Γ → Q.c ≤ γ →
    ∀ (Θ : Protection L) (K : Extra.Multi.Tariff) (z : ℝ), 0 ≤ z → ∀ A : Delays Θ,
      ∃ D : Delays Θ, Boost A D ∧
        ∃ F κ ℓ : ℕ → ℕ → ℝ,(∀ i j, z ≤ F i j) ∧ ∀ E : Delays Θ, Boost D E →
          Prices (raise s n) t (localSection G) E.betaEntry ∧ Stock.Priced E ∧
          Ringing (Builder.quote s T) F E ∧ Cosmos (chart G) (Builder.quote s T) E F κ ℓ ∧
            ∀ (Y : Bar E) (W : Wait Y) (a : Levels G), Paid W a → Doors.Budget a C p ∧
              Extra.Multi.Prepared B K (localSection G) a ∧ ∃ (M : Horizon a) (k : Kin M (chart G)), TopPath O T l Q a M k


end YM.PhysicalNext.ThroughLaunch
