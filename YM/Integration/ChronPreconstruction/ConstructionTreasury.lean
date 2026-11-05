import YM.Integration.ChronPreconstruction.ConstructionCustody
import YM.Integration.ChronPreconstruction.ClockTreasury

/-! The existing engageWithCustody constructs one literal Run.mk.
The complete pre-Rolls treasury receipt is transported along its exact
Levels equality, retaining every original Funded/Chron/custody output. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.R2I.ChronJoint
open Function Filter Set MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
open Campaign
set_option quotPrecheck false
open Boutique
open Daisy.Charity.RG12

theorem selectRunWithTreasury (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) {Λ: Levels G → Prop} (Δ : Decal G)(b:ℝ)(hb:0<b)(h:G.Simple)(hL:EventuallyPaid Λ) :
    ∃ (R:Run G)(T:Campaign R), R.family.path.levels.clock.kernel.penalty=b ∧
      Λ R.family.path.levels ∧ YM.Integration.CalendarTreasuryPurchase.TreasuryFunded R.family.path.levels ∧ Nonempty (Pillars R T) ∧ Funded Δ R T ∧ Stagehands.News R.kit Ω ∧
      ∃ Θ v, ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v := by
  let Q (i:ℕ):= i+2
  obtain ⟨M,P,A,X,Y,K,c,H,hAmp,hWild,hB,hF,hP,hX,hT,hY,hK,hQ,hHalo,hΛ,hTreasury,hA,
    ξ,v,t,a,D,Φ,θ1,hCustody,hν,hφ,hv,hψ,UΩ,hP',hZ⟩ := allFactorWithTreasury (Ω:=Ω) (ℋ:=ℋ) h hb Δ Q (fun i j hij=>Nat.add_le_add_right hij _) (fun _=>Nat.le_add_left ..) Λ hL
  obtain ⟨R,T,hR,hG,hN,hW,hU,hK',hA',hAddr,hlim,hS,Θ,hcR,hΘ⟩ :=
    engageWithCustody (Ω:=Ω) (ℋ:=ℋ) h Δ (q:=Q) (tendsto_atTop_mono (f:=id) (fun i=> Nat.le_add_right ..) tendsto_id) hA hQ hK hY hX Φ H hAmp hWild θ1 UΩ hCustody hν hφ hP' hv hψ hZ
  rw [← hW] at hB hF hHalo hT hΛ hTreasury hP
  exact ⟨R, T, hB, hΛ, hTreasury, hN,
    { localBudget := hK'.original
      attentive := hA'
      logCopy := hlim
      locrian := hR
      wild := hG
      silk := hS
      poly := hU
      fixed := hAddr
      tic := hT
      halo := hHalo
      paced := hF
      stoves := hP
      hasSky := ⟨UΩ, Θ, hΘ⟩ }, hK'.news, ⟨Θ, UΩ, hcR, hΘ⟩⟩

end YM.PhysicalNext.Repeat.Legato.R2I.ChronJoint
