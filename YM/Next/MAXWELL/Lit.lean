import YM.Bid.Scope
import YM.Next.MAXWELL.AwayTeam
import YM.Next.MAXWELL.Descent
import YM.Next.MAXWELL.Scenes
import YM.Work.A09
import YM.Work.A10
import YM.Work.A12






/-!
# RPort0 and RFree

Actual Maxwell comparator data and clients. Stress normalization takes
any real τ ≠ 0. Construction of Family, subsequences and comparison to
YM not asserted or inferred here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Analysis MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
open Climb
variable {G : Gauge}

def herald (R : Register G) (τ : ℝ) (hτ : τ≠0) : Lighthouse R where
  W := scheme R.grid
  K := gear R.grid
  J := τ • original R.grid
  κ := -τ
  hκ := neg_ne_zero.mpr hτ

theorem shines (R : Register G) (h : G.Simple) (τ : ℝ) (hτ : τ≠0) :
    (herald R τ hτ).Goes R (hierarchy R.grid).spin := by
  refine ⟨scheme_filters R.grid,scheme_derives R.grid,phase_orientation R.grid,gear_laws R.grid,gear_motion R.grid,beacon_signal R.grid τ,born h R.grid le_rfl,?_⟩
  obtain ⟨n,H⟩ := scanner R.grid h
  refine ⟨n,fun d hd => ?_⟩
  obtain ⟨L,hL,hL2,V⟩ := H d hd
  refine ⟨{ m := L.m, rows := L.rows, reads := L.reads, stimulated := L.stimulated },hL,hL2,V⟩

/-- Caller passes *the same* Family as in later extraction. -/
theorem maxwell_supplies (C : Family G) (h : G.Simple) (τ : ℝ) (hτ : τ≠0) :
    ∃ T : Org.MaxwellData C,T.T=herald C.book τ hτ ∧ T.vacuum=voyage C.labels :=
  Bid.masts Work.A12.answer Work.A10.answer Work.A09.answer (hierarchy C.labels) (herald C.book τ hτ)
    (shines C.book h τ hτ) (voyage C.labels) (launched C.labels) (erasing C.labels h)



open Ortho Org


end YM.Maxwell.Free
