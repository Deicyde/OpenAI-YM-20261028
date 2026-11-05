import YM.FullVolume.Cross
import YM.Integration.NativeComponentRecipe
import YM.Integration.NativePreselectedPostnumericPeriodRun

/-!
# Bind the native component recipe to the original constructed Run

Only the original raised-Sheet identity, quote identity and retained
numerical receipts are used. Every row is on R.family.path.levels and the
actual R.alloy.B.M. No replacement Family, Horizon or kernel is selected.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunNativeComponentRecipe
open Lattice RG RG.Supply Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open NativeComponentRecipe

variable {G : Gauge}

def postnumeric (s : Sheet G) (T : MapPrices) (C : Choice s)
    (lengths : ℕ → ℕ) (_ : ℕ) : ℕ → ℝ :=
  post s T C lengths

theorem on_run (R : Run G) (s : Sheet G) (T : MapPrices)
    (C : Choice s) (n : ℕ → ℕ)
    (hsheet : R.metals.p = ThroughLaunch.raise s n)
    (hquote : R.metals.K = ThroughLaunch.raging s T)
    (hfloor : floor s T C ≤ n)
    (hpaid : NativePostLengthPayment.StagePaid
      (post s T C (fun i => (R.family.path.levels.clock.factor i).val))
      R.family.path.levels) :
    Realized s T C R.family.path.levels R.alloy.B.M := by
  have hk : R.family.path.levels.clock.kernel = s.kernel := by
    calc
      _ = R.metals.p.kernel := R.alloy.B.valid.kernel
      _ = s.kernel := by rw [hsheet]
  have hs : R.family.path.levels.clock.stage = s.profile := by
    calc
      _ = R.metals.p.profile := R.alloy.B.valid.stage
      _ = s.profile := by rw [hsheet]
  have hlengths : R.family.path.levels.clock.factor = R.rolls.L :=
    R.alloy.B.valid.lengths
  have hbuy (i : ℕ) :
      floor s T C i ≤ (R.family.path.levels.clock.factor i).val := by
    have heq : R.metals.p.floorL i = n i := by rw [hsheet]
    have hn : n i ≤ (R.rolls.L i).val := by
      simpa only [heq] using (R.rolls.large i).need
    exact (hfloor i).trans (by simpa only [hlengths] using hn)
  have hH : R.alloy.B.M.Suffices (ThroughLaunch.raging s T) := by
    rw [← hquote]
    exact R.alloy.B.plan
  exact NativeComponentRecipe.realize s T C R.family.path.levels
    R.alloy.B.M hk hs hbuy hpaid hH

def Attached (R : Run G) : Prop :=
  ∃ (s : Sheet G) (T : MapPrices) (C : Choice s) (n : ℕ → ℕ),
    s.floorL ≤ n ∧ floor s T C ≤ n ∧
    R.metals.p = ThroughLaunch.raise s n ∧
    R.metals.K = ThroughLaunch.raging s T ∧
    NativeDiagonalClockRequest.PaidRequests (numeric s T C)
      R.family.path.levels ∧
    NativeDiagonalClockRequest.PaidRequests
      (postnumeric s T C (fun i => (R.family.path.levels.clock.factor i).val))
      R.family.path.levels ∧
    NativePostLengthPayment.StagePaid
      (post s T C (fun i => (R.family.path.levels.clock.factor i).val))
      R.family.path.levels ∧
    Realized s T C R.family.path.levels R.alloy.B.M

theorem of_preselection (R : Run G)
    (h : R2I.RG05Joint.PostnumericPreselection
      (fun s (_ : MapPrices) => Choice s) floor numeric postnumeric R) :
    Attached R := by
  obtain ⟨s, T, C, n, hbase, hfloor, hsheet, hquote, hnumeric, hpost, hstage⟩ := h
  exact ⟨s, T, C, n, hbase, hfloor, hsheet, hquote, hnumeric, hpost, hstage,
    on_run R s T C n hsheet hquote hfloor hstage⟩

end YM.Integration.ActualRunNativeComponentRecipe
end
