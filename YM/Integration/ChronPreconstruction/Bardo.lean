import YM.R2I.Campaign.Bardo
import YM.Integration.ChronPreconstruction.Fares

/-! Retain the fixed calendar through the original trace and weak
continuum suppliers, without changing their witnesses. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.R2I.ChronJoint
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
open YM.MergeProof.East
-- Another grantor for buying universal weak supplies. Can still extend before-L clocks, after-L Delays, extra Paid W and layouts. retains
variable (hG:G.Simple){K:KernelChoices}(hK :∀ p : Patch,p.Branches K G){v:Orders}(hp:ThroughLaunch.Draft v)(Q:ℕ→ℕ) (hQ:Monotone Q)(hQ':∀ i,1 ≤ Q i)
include hp hQ hQ' hK hG
theorem plentiful (Ω : RemainderComparison.Chron.Contemple G) {ξq ωt ωv:ℝ} (θ1:Luna.Tableau ξq 300) (hu:Jams.sphere ξq ωv ωt) (hQ2:∀ i,2≤ Q i)(he:∀ i,100 ≤ v.supportExp i) (Δ:Daisy.Charity.RG12.Decal G) : ∃ (s:Sheet G)(T:MapPrices)(Y:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.bountyV s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J' ∧ Jams.Degree X.shape X.scout V' ∧ Jams.Savvy X.scout X.target V' ξq ωv ωv ωt ∧ Roof.Roofing X ωt ωt ∧ Planned.Port.AtTop B.kin ∧ Stationary.Artes.Cadre F B.kin ∧ Next.Free.Amplify B.M ∧ Jams.PaysW X.shape ωv V' ∧ Luna.Spire θ1 X.shape (Luna.costP M.p P) V' ∧ (∀ i:ℕ,100 ≤ (B.a.budget i).supportExponent) ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (X.span i j)) ≤ (P.L i).val) ∧ (∃ U₁, FullVolume.Paint.Tower.Sav G M.p.profile Y θ1 U₁ P.L ∧ Mallow.Canyon ξq X.shape Y θ1 U₁ V') ∧ Jams.Wild X.shape V' ∧ Mallow.AccordV X.shape Q V')∧∃ (b:Bandage X Y K'), Extras Ω Δ b ∧ Unlatched b Q (fun T t S _ => let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∀ f:Extraction.Order, CompleteWeak Z f ∧ Trace.Over.Gallery Z f) := by
    obtain ⟨s,T,Y,K',hs,hv,τ,hτ,hA⟩:= richFares (Ω:=Ω) hG hK hp Q hQ hQ' θ1 hu he Δ
    have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hv.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
    obtain ⟨u,hU⟩:= posters s (ThroughLaunch.raging s T) ho
    obtain ⟨O⟩:= Next.Rank.exists_budget G
    obtain ⟨uB,hU'⟩:= submits (ThroughLaunch.raging s T) s ho
    obtain ⟨uW,hUW⟩:= Trace.Perfect.vroom s
    refine ⟨s,T,Y,K',hs,hv, (τ ⊔ u)⊔(uB⊔(uW⊔Trace.Terrace.ctl)),hτ.trans (le_sup_left.trans le_sup_left),fun k hk =>?_⟩
    obtain ⟨hk,ht₀⟩:=sup_le_iff.mp hk; obtain ⟨hi₁,hi₂⟩:=sup_le_iff.mp ht₀; obtain ⟨hw0,hCtl⟩:=sup_le_iff.mp hi₂
    have heSup:=hv
    obtain ⟨hk,hL⟩:= sup_le_iff.mp hk; obtain ⟨hN,hK⟩:= hA k hk; intro M
    have hz : RelayP M.p M.K u:=by
       obtain ⟨b,F,ψ,he,v⟩:= hU.buys
       refine ⟨b,F,ψ,he,v.same,?_,?_,?_⟩
       · intro i; refine ⟨(v.buys i).1,(v.buys i).2⟩
       · intro i; exact ⟨(v.shops i).1⟩
       intro i d j;exact v.lifts i d j
    refine ⟨hN,fun P=> ?_⟩; obtain ⟨U,H⟩:= hK P
    refine ⟨U,fun w hw Q₀ e=>?_⟩; obtain ⟨F,hF⟩:= H w hw Q₀ e
    refine ⟨F,fun u0 hv=>?_⟩; obtain ⟨θ,hθ,hB⟩:= hF u0 hv
    refine ⟨θ,hθ,fun Ht J T0=>?_⟩
    obtain ⟨V₁,h1,hΩ⟩:= Trace.Terrace.staircase (X:=M.p) hCtl T0
    obtain ⟨D0,hd⟩:=hUW k hw0 P
    let T2: Delays θ:= {V₁ with betaEntry:=D0 ⊔ V₁.betaEntry}
    obtain ⟨T3,h2,h3⟩:= Trace.Margin.flows T2 hG; obtain ⟨T4,ht₄,hβ⟩:= Quince.rise_B T3
    obtain ⟨V,hV,hW⟩:= hB Ht J T4
    have hζ:DelayLe V₁ V:= (show DelayLe V₁ T2 from ⟨fun i=>le_max_right ..,le_rfl,le_rfl,le_rfl⟩).trans (h2.trans (ht₄.trans hV));
    have hcT:(D0:ℕ→ℝ)≤V.betaEntry:= fun i=>le_trans (b:=T2.betaEntry i) (le_max_left ..) ((h2.trans (ht₄.trans hV)).beta i)
    refine ⟨V,h1.trans hζ,fun V' hv D W=>?_⟩; obtain ⟨Z,hZ,hW⟩:= hW V' hv D W
    obtain ⟨J',hN₁,hL,hK,H⟩:= sponsored hG M.K O (Next.Foundations.chart G) (Next.Foundations.chart_ok G) _ hz (fun i=>(hL i).trans (P.large i).need) Z
    let z(s):= ∑ i∈Finset.range (s+1), generator G i
    have ht':∀ i j,i ≤ j → generator G i ≤ z j:= fun i j h=> Finset.single_le_sum (fun i _=>by unfold generator; positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le h)); have hz₁(i):0 ≤ z i:=Finset.sum_nonneg (fun i _=> by unfold generator;positivity)
    have hvU:RelaySky M.K uB (X:=M.p):=by
        obtain ⟨a,hM,h,P,V,hN,hB⟩:=hU'.asks; refine ⟨a,hM,h,P,V,⟨hN.later,?_,hN.pin⟩,hB⟩; intro i j hi x; have ht:= hN.costs i j hi x; refine ⟨ht.1,fun k hk L hL=> ?_⟩; have hx:= ht.2 k hk L hL; exact ⟨hx.reg,hx.coast,hx.commission,hx.merit⟩
    obtain ⟨W0,hψ,hΞ,hQ',H'⟩:= embalms M.K uB hvU O (Next.Foundations.chart G) (Next.Foundations.chart_ok G) (fun i=>(hi₁ i).trans (P.large i).need) hG z hz₁ J'
    refine ⟨W0,⟨hZ.1.trans (hL.trans hΞ),hZ.2.1.trans (hN₁.trans hψ),hZ.2.2.trans (hK.trans hQ')⟩,fun W ha hb hc a h hi=>?_⟩
    obtain ⟨T',B,hF,R,hR,b,hExt,hAll⟩:= hW W (hL.trans (hΞ.trans ha)) (hK.trans (hQ'.trans hb)) (hN₁.trans (hψ.trans hc)) a h hi
    refine ⟨T',B,hF,R,hR,b,hExt,?_⟩; intro T'' htN t htp Xf G0 C hxB hp hg
    obtain ⟨hX,hq,hπ,hvv,hSS,hn,hL',-⟩ := hAll T'' htN t htp Xf G0 hxB hp hg
    refine ⟨hX,hq,hπ,hvv,hSS,hn,hL',fun F=>?_⟩
    obtain ⟨hC,hM,hA,hS,hL₀,S',hA,hC,h₃⟩:= hX.reception
    have hp:= Next.Rank.East.enclosing Xf hX.freight hM
    have hP:Paid W0 B.a:=retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid
    have hU:= H' C hP S' hC hM hp
    have hΓ:Trace.Terrace.supportQ B.a:= by
         apply Filter.Eventually.of_forall; intro i; rw[params_eq B.valid]; exact le_trans (by norm_num: (4:ℝ)≤100) (by change (_:ℝ) ≤ (s.profile _).supportExponent; rw[heSup.prices]; exact he _)
    let Alloy0: Alloy M P := Alloy.mk _ θ V' D W T' B
    have hNe:Quince.Ordeal B.a:=Quince.ordered (A:=Alloy0) (hβ _ (hV.trans hv))
    refine ⟨H C (retains_budget (hψ.trans hc) (fun i=>⟨hΞ i|>.trans (ha i),hQ' i|>.trans (hb i)⟩) B.valid) S' hC hM hp _ _ _ _ _ _ G0 hS F,?_⟩
    have hS0:=hΩ _ (hζ.trans hv) D W B.a B.valid; have hV1:=h3 _ (ht₄.trans (hV.trans hv)) D W B.a B.valid
    have htF:Trace.Terrace.Sceptre C K':= Quince.attain b T'' hX.nest hG hExt.tracing hNe hM
    obtain ⟨L,hL⟩:= Ultrafilter.exists_le F.fuse
    obtain ⟨Tℓ,hT⟩:= Trace.Margin.agenda (t:=t) (U:=Xf) b hX.nest (hd _ _ (hcT.trans hv.beta) D W B.a B.valid) hV1 hΓ hG L (Trace.Terrace.link_mesh hL) (Trace.Terrace.link_period hL)
    exact Trace.Over.gang hM hG hS0 hq hS htF hΓ hL hT hS.costs.night (Filter.Eventually.of_forall (fun i=> hQ2 _)) (hV1 |> Trace.Margin.honor _) S' _ _ ht' hU
end YM.PhysicalNext.Repeat.Legato.R2I.ChronJoint
