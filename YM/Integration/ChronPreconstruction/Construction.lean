import YM.R2I.Campaign.Accepted
import YM.Integration.ChronPreconstruction.Clock

/-! One original Run, Campaign and transfer factory retain both the full
R2I Funded package and the Chron library bought for the fixed calendar.
The calendar is fixed before this Run is chosen. -/
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
section
variable {M : Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}{b:Bandage X Y K}
/- Construction independent of p sampling. Again from DensityClock.lean. -/
lemma engage (Ω : RemainderComparison.Chron.Contemple G) (h:G.Simple){q:ℕ→ℕ} (Δ : Daisy.Charity.RG12.Decal G) (hQs:Tendsto q atTop atTop)
    (hU:Attentive b q) (hQ:Mallow.AccordV X.shape q A.delay) (hBa: Extras Ω Δ b) (hYf:Mallow.FrameAccord X.target P A.delay)
    (h100:∀ i,(A.B.a.params i).supportExponent = 100){c u t τ:ℝ}{L: Roof.Lyrics X u u}(Φ:Muse.Plato L c t t τ) (hP : Stationary.Artes.Cadre A.post A.B.kin)(he : Next.Free.Amplify A.B.M)(hy:Jams.Wild X.shape A.delay)(θ1:Luna.Tableau c 300) (v:ℕ→ℕ→ℝ)(hν:Jams.PaysW X.shape t A.delay)(hΩ:Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay)(hPγ:FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 v P.L) (hv:∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent)(hψ:∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) (hG:Mallow.Canyon c X.shape Y θ1 v A.delay):∃ (R:Run G)(T:Campaign R), Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay ∧ Nonempty (Pillars R T)  ∧ R.family.path.levels=A.B.a ∧ Mallow.AccordV R.kit.shape R.Q R.alloy.delay ∧
      Extras Ω Δ R.b ∧ Attentive R.b R.Q ∧ (∀ i,(R.alloy.B.a.params i).supportExponent=100) ∧
      Tendsto R.Q atTop atTop ∧ Mallow.FrameAccord R.kit.target R.rolls R.alloy.delay ∧ ∃ Θ, Sky R T Θ v :=by
    let C:=b
    choose s hp using fun d:ℕ=> ((eventually_ge_atTop 1).and (A.B.a.fits.deep.eventually_ge_atTop (d+3))).exists
    have hb (d): 1 ≤ s d:= hp d|>.1
    obtain ⟨T,⟨Z⟩,hD⟩:= FullVolume.rodB X Φ
    let ht(d):d+3 ≤ (Issue.trail T).levels.clock.J (s d):= hp d|>.2
    have hZ:=Z.receipts
    choose B hB using fun N p m (hm : m < N)=> Boutique.taste h (F₀:=L) hZ (hD N p) hm
    let U (N p:ℕ):Branch X T.history N p 0 := ⟨T.choice,fun i _ hm=> hZ.samples h _ _ _ hm,fun m _ he=> B N p m he⟩ -- dots need explicit
    obtain ⟨V,hC,hY,H⟩:= Bandage.coming h b hZ s ht U; let R : Run G:= ⟨M,P,A,X,Y,K,b,q,hU.ahead,T,Z,s,ht,ease U,V,hC,fun N m p hx=> Boutique.mountain T (B N p m hx),hY⟩
    let T':Campaign R:= ⟨c,τ,u,t,L,Φ,hD⟩
    exact ⟨R,T',⟨hP,he⟩,hy,⟨hb,U,rfl,fun N p m hm=> hB N p m hm,H⟩,rfl,hQ,hBa,hU,h100,hQs,hYf,θ1,⟨hv,hψ,hν,hΩ,hPγ,hG⟩⟩
end

open Daisy.Charity.RG12

theorem selectRun (Ω : RemainderComparison.Chron.Contemple G) {Λ: Levels G → Prop} (Δ : Decal G)(b:ℝ)(hb:0<b)(h:G.Simple)(hL:EventuallyPaid Λ) :
    ∃ (R:Run G)(T:Campaign R), R.family.path.levels.clock.kernel.penalty=b ∧
      Λ R.family.path.levels ∧ Nonempty (Pillars R T) ∧ Funded Δ R T ∧ Stagehands.News R.kit Ω := by
  let Q (i:ℕ):= i+2
  obtain ⟨M,P,A,X,Y,K,c,H,hAmp,hWild,hB,hF,hP,hX,hT,hY,hK,hQ,hHalo,hΛ,hA,
    ξ,v,t,a,D,Φ,θ1,hν,hφ,hv,hψ,UΩ,hP',hZ⟩ := allFactor (Ω:=Ω) h hb Δ Q (fun i j hij=>Nat.add_le_add_right hij _) (fun _=>Nat.le_add_left ..) Λ hL
  obtain ⟨R,T,hR,hG,hN,hW,hU,hK',hA',hAddr,hlim,hS,Θ,hΘ⟩ :=
    engage (Ω:=Ω) h Δ (q:=Q) (tendsto_atTop_mono (f:=id) (fun i=> Nat.le_add_right ..) tendsto_id) hA hQ hK hY hX Φ H hAmp hWild θ1 UΩ hν hφ hP' hv hψ hZ
  rw [← hW] at hB hF hHalo hT hΛ hP
  exact ⟨R, T, hB, hΛ, hN,
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
      hasSky := ⟨UΩ, Θ, hΘ⟩ }, hK'.news⟩

end YM.PhysicalNext.Repeat.Legato.R2I.ChronJoint
