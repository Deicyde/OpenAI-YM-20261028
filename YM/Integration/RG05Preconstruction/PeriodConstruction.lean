import YM.Integration.ChronPreconstruction.ConstructionTreasury
import YM.Integration.RG05Preconstruction.PeriodClock

/-! One literal Run.mk retains the original purchases and the exact period
registry. Its original Metals value is exported explicitly so the new Arena
receipt applies to this Run's actual K and O, as well as its Levels. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
open YM.Integration.RG05Preconstruction
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
open YM.Integration.NativeSelection
section
variable {M : Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:ℕ→ℝ}{K:Bid.Worth}{b:Bandage X Y K}
/- Construction independent of p sampling. Again from DensityClock.lean. -/
lemma engageWithCustodyFactor (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) (h:G.Simple){q:ℕ→ℕ} (Δ : Daisy.Charity.RG12.Decal G) (hQs:Tendsto q atTop atTop)
    (hU:Attentive b q) (hQ:Mallow.AccordV X.shape q A.delay) (hBa: YM.Integration.RG05Preconstruction.Extras Ω Δ b) (hYf:Mallow.FrameAccord X.target P A.delay)
    (h100:∀ i,(A.B.a.params i).supportExponent = 100){c u t τ:ℝ}{L: Roof.Lyrics X u u}(Φ:Muse.Plato L c t t τ) (hP : Stationary.Artes.Cadre A.post A.B.kin)(he : Next.Free.Amplify A.B.M)(hy:Jams.Wild X.shape A.delay)(θ1:Luna.Tableau c 300) (v:ℕ→ℕ→ℝ)(hcR:ℋ.items A.post Y K θ1 A.B.a)(hν:Jams.PaysW X.shape t A.delay)(hΩ:Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay)(hPγ:FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 v P.L) (hv:∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent)(hψ:∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) (hG:Mallow.Canyon c X.shape Y θ1 v A.delay)
    (prediction : FundedCompanySelection.Prediction G) (hPrediction : prediction X) :
    ∃ (R:Run G)(T:Campaign R), prediction R.kit ∧ R.metals = M ∧ Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay ∧ Nonempty (Pillars R T)  ∧ R.family.path.levels=A.B.a ∧ Mallow.AccordV R.kit.shape R.Q R.alloy.delay ∧
      YM.Integration.RG05Preconstruction.Extras Ω Δ R.b ∧ Attentive R.b R.Q ∧ (∀ i,(R.alloy.B.a.params i).supportExponent=100) ∧
      Tendsto R.Q atTop atTop ∧ Mallow.FrameAccord R.kit.target R.rolls R.alloy.delay ∧ ∃ Θ, ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v :=by
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
    exact ⟨R,T',hPrediction,rfl,⟨hP,he⟩,hy,⟨hb,U,rfl,fun N p m hm=> hB N p m hm,H⟩,rfl,hQ,hBa,hU,h100,hQs,hYf,θ1,hcR,⟨hv,hψ,hν,hΩ,hPγ,hG⟩⟩
/-- Engage the original factor with its metals and all campaign receipts. -/
lemma engageWithCustodyMetals (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) (h:G.Simple){q:ℕ→ℕ} (Δ : Daisy.Charity.RG12.Decal G) (hQs:Tendsto q atTop atTop)
    (hU:Attentive b q) (hQ:Mallow.AccordV X.shape q A.delay) (hBa: YM.Integration.RG05Preconstruction.Extras Ω Δ b) (hYf:Mallow.FrameAccord X.target P A.delay)
    (h100:∀ i,(A.B.a.params i).supportExponent = 100){c u t τ:ℝ}{L: Roof.Lyrics X u u}(Φ:Muse.Plato L c t t τ) (hP : Stationary.Artes.Cadre A.post A.B.kin)(he : Next.Free.Amplify A.B.M)(hy:Jams.Wild X.shape A.delay)(θ1:Luna.Tableau c 300) (v:ℕ→ℕ→ℝ)(hcR:ℋ.items A.post Y K θ1 A.B.a)(hν:Jams.PaysW X.shape t A.delay)(hΩ:Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay)(hPγ:FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 v P.L) (hv:∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent)(hψ:∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) (hG:Mallow.Canyon c X.shape Y θ1 v A.delay):∃ (R:Run G)(T:Campaign R), R.metals = M ∧ Locrian R∧ Jams.Wild R.kit.shape R.alloy.delay ∧ Nonempty (Pillars R T)  ∧ R.family.path.levels=A.B.a ∧ Mallow.AccordV R.kit.shape R.Q R.alloy.delay ∧
      YM.Integration.RG05Preconstruction.Extras Ω Δ R.b ∧ Attentive R.b R.Q ∧ (∀ i,(R.alloy.B.a.params i).supportExponent=100) ∧
      Tendsto R.Q atTop atTop ∧ Mallow.FrameAccord R.kit.target R.rolls R.alloy.delay ∧ ∃ Θ, ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v  := by
  simpa only [FundedPredictionSupply.Always, true_and] using
    (engageWithCustodyFactor Ω ℋ h Δ hQs hU hQ hBa hYf h100 Φ hP he hy θ1 v hcR hν hΩ hPγ hv hψ hG
      (@FundedPredictionSupply.Always G) trivial)

end

open Daisy.Charity.RG12

theorem selectRunWithTreasuryPeriod (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) {Λ: Levels G → Prop} (Δ : Decal G)(b:ℝ)(hb:0<b)(h:G.Simple)(hL:EventuallyPaid Λ) :
    ∃ (R:Run G)(T:Campaign R), R.family.path.levels.clock.kernel.penalty=b ∧
      Λ R.family.path.levels ∧ YM.Integration.CalendarTreasuryPurchase.TreasuryFunded R.family.path.levels ∧
      YM.Integration.CommonPeriodPurchase.Funded R.metals.K R.metals.O R.family.path.levels ∧ Nonempty (Pillars R T) ∧ Funded Δ R T ∧ Stagehands.News R.kit Ω ∧ ReadoutPurchase R.b ∧
      ∃ Θ v, ℋ.items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Sky R T Θ v := by
  let Q (i:ℕ):= i+2
  obtain ⟨M,P,A,X,Y,K,c,H,hAmp,hWild,hB,hF,hP,hX,hT,hY,hK,hQ,hHalo,hΛ,hTreasury,hPeriod,hA,
    ξ,v,t,a,D,Φ,θ1,hCustody,hν,hφ,hv,hψ,UΩ,hP',hZ⟩ := allFactorWithTreasuryPeriod (Ω:=Ω) (ℋ:=ℋ) h hb Δ Q (fun i j hij=>Nat.add_le_add_right hij _) (fun _=>Nat.le_add_left ..) Λ hL
  obtain ⟨R,T,hMetals,hR,hG,hN,hW,hU,hK',hA',hAddr,hlim,hS,Θ,hcR,hΘ⟩ :=
    engageWithCustodyMetals (Ω:=Ω) (ℋ:=ℋ) h Δ (q:=Q) (tendsto_atTop_mono (f:=id) (fun i=> Nat.le_add_right ..) tendsto_id) hA hQ hK hY hX Φ H hAmp hWild θ1 UΩ hCustody hν hφ hP' hv hψ hZ
  rw [← hW] at hB hF hHalo hT hΛ hTreasury hPeriod hP
  have hPeriodR : YM.Integration.CommonPeriodPurchase.Funded
      R.metals.K R.metals.O R.family.path.levels := by
    rw [hMetals]
    exact hPeriod
  exact ⟨R, T, hB, hΛ, hTreasury, hPeriodR, hN,
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
      hasSky := ⟨UΩ, Θ, hΘ⟩ }, hK'.news, hK'.readout, ⟨Θ, UΩ, hcR, hΘ⟩⟩

end YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
