import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Postsale
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Soft.Royal
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Postsale for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis
open scoped Topology BigOperators Classical
variable {G : Gauge} {X : RG.Supply.Sheet G} (B : MapPrices)
variable (O : HaarBudget G) (J : ChartRatio G) {w : Rolls X} {D : Protection w} {T : Delays D} {Z : Bar T}
open Pump
structure VentsSky {C : Family G} (B : Binding C) (v : Purse) (J : ChartRatio G) (l d : ℝ) (i : ℕ):Prop where
  rate (k : ℕ) (hk : Station.widthSky C.path.levels v.band i ≤ k) (ht : k ≤ i): Costs (C.path.levels.params k) G (clim C.path.levels i)
  great (k : ℕ) (hk : Station.widthSky C.path.levels v.band i ≤ k) (ht : k < i):
    let A:= C.path.levels; let y:=clim A i; let j:=A.clock.J (k+1); let L:=A.clock.factor j
    ∃ b:ℝ, 0 ≤ b ∧ i-k ≤ stretch L.val b y ∧ TimingSky (tell B k) J j L v b l d y

-- collect publication for active stage. Don't advertise off-stage positive Standing. d>0 not actually needed to use schedule gate outside Active.E.era

end YM.PhysicalNext.InteractingRank.Soft
