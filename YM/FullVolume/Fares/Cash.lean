import YM.FullVolume.Fares.Time
/- Acquire tariff & eventual canopy budgets.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} {T:Campaign R}
set_option quotPrecheck false
local notation "P"=> R.alloy.B.a
local notation "X"=> R.kit
local notation "D"=> R.rolls
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
namespace Sky
variable {Θ:Luna.Tableau T.width 300}{v:ℕ→ℕ→ℝ}(hk:Sky R T Θ v)
open Pressure
local notation "n!"=> Fintype.card I
variable (d:I→ℕ) (x:(i:I)→ ((Labels.frames G).level (d i)).Coeff)
include hk
lemma hired: ∀ᶠ b:ℕ in atTop,∀ᶠ m:ℕ in atTop,Economics T Θ v d x b m:= by
    have hp(i:I) := hk.salaries (d i) (n!) ‖x i‖
    filter_upwards [hk.entry.toTick, hk.deploy (n:=n!), eventually_all.mpr (fun i:I=> (hp i).1.toTick), eventually_all.mpr (fun i:I=>(hp i).2.1.toTick),eventually_all.mpr (fun i:I=>(hp i).2.2.1.toTick),eventually_all.mpr (fun i:I=> (hp i).2.2.2.toTick)] with b hB huv hE hK hU hT
    filter_upwards [hB,hk.launches.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop 8),hk.launches.eventually_ge_atTop 512, (P).fits.deep.eventually_ge_atTop (n!), hk.canopy b,eventually_all.mpr hE,eventually_all.mpr hK,eventually_all.mpr hU,eventually_all.mpr hT] with m hm hs hg hD hΩ hE hK hU hT
    have hx:= (hk.presents m).stars _ (hD.trans ((P).fits.mono m.le_succ))
    exact ⟨hs,(by norm_num : (1:ℝ)≤100).trans (hk.supports m),hk.slow m, hg,hm,hΩ,hk.receives m,hE,hK,hU,hT,hx.capital,hx.covered,hx.height,hx.heights,hx.issued,hx.crowned, fun r hr=>(huv m r hr).1,fun r hr=>(huv m r hr).2⟩
end Sky
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Sky.hired
