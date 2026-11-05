import YM.Integration.RG05Preconstruction.Bardo
import YM.Integration.ChronPreconstruction.ClockCustody
import YM.Integration.CalendarTreasuryPurchase
import YM.Integration.CommonPeriodPurchase

/-! Buy the literal period registry floor together with the original Calendar
floor before Rolls. Its later beta gate is inserted into the same monotone
delay chain. All original Chron, custody and numerical receipts remain. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
open YM.Integration.RG05Preconstruction
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
open Daisy.Charity.RG12

-- Unconditional existence through the actual Wcmain, ranks and Seed.
variable (hG:G.Simple)
include hG
theorem allFactorWithTreasuryPeriod (Ω : RemainderComparison.Chron.Contemple G) (ℋ : CustodyR G) {β:ℝ} (h:0<β)
    (δ : Decal G) (PB:ℕ→ℕ) (hPB:Monotone PB) (hPB2:∀ i, 2 ≤ PB i) (Λ: Levels G → Prop) (hΛ:EventuallyPaid Λ) : ∃ (M:Metals G)(P:Rolls M.p)(A:Alloy M P)(X:Factor A)(Y:ℕ→ℝ)(K:Bid.Worth)(b:Bandage X Y K),
    Stationary.Artes.Cadre A.post A.B.kin ∧ Next.Free.Amplify A.B.M ∧ Jams.Wild X.shape A.delay ∧ A.B.a.clock.kernel.penalty=β ∧ Flick A.B.a ∧ OPE.Therm.Poetry A.B.a ∧
    (∀ i, (A.B.a.params i).supportExponent = 100) ∧ OPE.Log.OnBudget A.B.a ∧
    Mallow.FrameAccord X.target P A.delay ∧ YM.Integration.RG05Preconstruction.Extras Ω δ b ∧ Mallow.AccordV X.shape PB A.delay ∧
    OPE.HaloGate A.B.a ∧ Λ A.B.a ∧ YM.Integration.CalendarTreasuryPurchase.TreasuryFunded A.B.a ∧ YM.Integration.CommonPeriodPurchase.Funded M.K M.O A.B.a ∧ Attentive b PB ∧ ∃ ξ t τ a, ∃ (V:Roof.Lyrics X t t), Muse.Plato V ξ a a τ ∧ ∃ θ1:Luna.Tableau ξ 300,ℋ.items A.post Y K θ1 A.B.a ∧ Jams.PaysW X.shape a A.delay ∧ Luna.Spire θ1 X.shape (Luna.costP M.p P) A.delay ∧ (∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent) ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((M.p.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) ∧ ∃ UX,FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 UX P.L ∧ Mallow.Canyon ξ X.shape Y θ1 UX A.delay := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G β h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun _=>100⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= le_rfl
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    exact le_rfl
  obtain ⟨q,hq⟩:=Muse.concert.exists
  obtain ⟨θ1⟩:= Luna.Tableau.access 300 (show 1≤q by linarith [hq.1])
  let a':ℝ:= 1/1024; have hh:0<a':=by norm_num [a'];
  obtain ⟨t,ht,hu,hU⟩:=Jams.ball_on (q:=q) (s:=a') (r:=1) (by linarith [hq.1]) hh (by norm_num [a']) (by norm_num)
  obtain ⟨s,T,Y,K,hX,HStage,l,hL,hK⟩:= plentiful (Ω:=Ω) hG hp he PB hPB (fun i=> (show 1≤2 from by decide).trans (hPB2 i)) θ1 hU hPB2 hE δ
  have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [HStage.jets]; exact (le_max_right ..).trans (he.k i)) tendsto_id
  obtain ⟨R,hR⟩:= Pert.Dense.bulletin s (ThroughLaunch.raging s T) ho
  obtain ⟨O⟩:= Next.Rank.exists_budget G
  obtain ⟨treasury⟩ := YM.Integration.CalendarTreasuryPurchase.plan_exists hG s.kernel
  obtain ⟨periodPlan⟩ := YM.Integration.CommonPeriodPurchase.plan_exists G s.kernel
    (ThroughLaunch.raging s T) (Next.Foundations.chart G)
  let blockFloor := ((l ⊔ R) ⊔ treasury.floor) ⊔ periodPlan.floor
  have hOldFloor : l ⊔ R ≤ blockFloor := le_sup_left.trans le_sup_left
  let M := ThroughLaunch.bountyV s T blockFloor
  obtain ⟨⟨P⟩, H⟩ := hK blockFloor (le_sup_left.trans hOldFloor)
  have hz : Pert.Dense.Relay M.p M.K R:=by
     obtain ⟨b,F,ψ,he,v⟩:= hR.bulletin
     refine ⟨b,F,ψ,he,v.same,?_,?_,?_⟩
     · intro i; exact ⟨(v.buys i).1,(v.buys i).2⟩
     · intro i; exact ⟨(v.shops i).1⟩
     intro i d j;exact v.lifts i d j
  have hUQ : ∀ i, R i ≤ (P.L i).val := fun i =>
    (le_sup_right (a := l) (b := R) i).trans ((hOldFloor i).trans (P.large i).need)
  have hTreasuryFloor : ∀ i, treasury.floor i ≤ (P.L i).val := fun i =>
    ((show treasury.floor ≤ blockFloor from le_sup_right.trans le_sup_left) i).trans (P.large i).need
  have hPeriodFloor : ∀ i, periodPlan.floor i ≤ (P.L i).val := fun i =>
    ((show periodPlan.floor ≤ blockFloor from le_sup_right) i).trans (P.large i).need
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩
  obtain ⟨Ugate,-,hgate⟩ := OPE.halo_delay U
  obtain ⟨Ustep,hStep,hstep⟩:= flickDelay Ugate
  obtain ⟨Upo,hPo,hpo⟩:= OPE.Therm.poetry_delay Ustep
  obtain ⟨Ucl,hCl,hcl⟩:= hΛ _ _ _ Upo
  obtain ⟨Ucalendar, hCalendar, hCalendarPaid⟩ :=
    YM.Integration.CalendarTreasuryPurchase.buy (s := M.p) (L := P) (θ := θ) treasury hTreasuryFloor Ucl
  obtain ⟨Uperiod, hPeriod, hPeriodPaid⟩ :=
    YM.Integration.CommonPeriodPurchase.buy (s := M.p) (D := P) (θ := θ) periodPlan hPeriodFloor Ucalendar
  obtain ⟨Ubud,hBud,hbud⟩:= OPE.Log.aux_delay Uperiod
  obtain ⟨Usilk,hS1,hsilk⟩:= RG12Joint.silk_extra Ubud
  obtain ⟨Ucust,hCust,hCustody⟩:= ℋ.buys F Y K θ1 Usilk
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ Ucust
  obtain ⟨V',H',Hp'⟩:=Tent.quotes V hh
  obtain ⟨Vx,hx,hV⟩:=Muse.header hG V' hh q
  obtain ⟨D,-⟩:= Bar.exists_above Vx 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y0,-,H⟩:= hK Vx (H'.trans hx) D I
  let W0 : Wait D:= ⟨fun _ => 0,SharpGram.Dense.slim D,SharpGram.Dense.slimWindow hG D,0⟩
  obtain ⟨W2,_,hSlim,WP,hWP⟩ := Pert.Dense.slim_wait_for M.K O (Next.Foundations.chart G) W0 hG hz hUQ (Next.Foundations.chart_ok G) rfl
  obtain ⟨Y,hYT,hLate⟩:= SharpGram.Dense.loadBoth hG Y0 W2
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,hExt,hU⟩:= H Y hYT.ready hYT.range hYT.minL a ha hp
  obtain ⟨hA,hC,hM,hη,hW,hL,hU',hE,hR,hCσ,hPΩ,U₁,HΩ,hYe,hYv,hY₁,hYs,hAr⟩:=W
  have ht':= Hp' Vx hx
  obtain ⟨p,hh'⟩:= Tent.verses R ht' hR hE
  have hmCust := h₁.trans (H'.trans hx)
  have hm := hCust.trans hmCust
  have hs₃ := hS1.trans hm
  have hs₂ := hBud.trans hs₃
  have hsPeriod := hPeriod.trans hs₂
  have hsCalendar := hCalendar.trans hsPeriod
  have hs₁ := hCl.trans hsCalendar
  have hs₀ := hPo.trans hs₁
  have h100 (i): (B.a.params i).supportExponent = 100 := by
    rw [params_eq B.valid i]; exact HStage.prices (B.a.clock.J i)
  refine ⟨_,_,_,_,_,_,c,hCσ,hPΩ,hYs,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hstep Vx hs₀ _ _ B.a B.valid, hpo Vx hs₁ Y B.a B.valid,h100,hbud Vx hs₃ Y B.a B.valid,hsilk Vx hm _ _,hExt,hAr,hgate Vx (hStep.trans hs₀) Y B.a B.valid,hcl Vx hsCalendar _ Y B.a B.valid, hCalendarPaid Vx hsPeriod _ Y B.a B.valid, hPeriodPaid Vx hs₂ _ Y B.a B.valid, ?_, q,t,a',a',p,⟨hL,hU',by norm_num [a', FullVolume.Amp.glint],hq, ht', hR,hB.symm ▸ hV Vx (DelayLe.refl _) D Y a ha,by norm_num [a', FullVolume.Amp.glint],hh',hG, Drifting.pay B.valid⟩,θ1,hCustody Vx hmCust _ _ B.a B.valid,U₁,HΩ,hYe,hYv,hY₁⟩
  intro t u S v Xf K C hx hp ht
  obtain ⟨hX,hq,hπ,hv,hS,hn,hL',hGal⟩:= hU t u S v Xf K hx hp ht; refine ⟨hX,hq,hπ,hv,hS,hn,hL',hGal,?_⟩
  obtain ⟨hC,hM,hA,hS,hL₀,S',hA,hC,h₃⟩:= hX.reception
  exact ⟨hM,SharpGram.Dense.covered M.K O (Next.Foundations.chart G) WP hWP hSlim hLate B.valid S' hC hM (Next.Rank.East.enclosing Xf hX.freight hM)⟩

end YM.PhysicalNext.Repeat.Legato.R2I.RG05Joint
