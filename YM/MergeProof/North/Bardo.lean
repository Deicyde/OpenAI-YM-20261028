import YM.MergeProof.East.Gran
import YM.MergeProof.North.Bourse


/-! Calendared proof thru actual Base+Seed. Can pay more beforeL, delays and Wait. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
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
lemma himalayas (he:∀ i,100 ≤ v.supportExp i): ∃ (s:Sheet G)(T:MapPrices)(Y:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= ThroughLaunch.currency s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J')∧∃ (b:Bandage X Y K'), ∃ T t S D,Chateau b Q T t S D ∧ Stock.Tabs B.a ∧ (let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; Velour Z (renal B.a) (mutt B.a Q) D ∧ ∀ f:Extraction.Order, CompleteWeak Z f) := by
    obtain ⟨s,T,Y,K',hs,hv,τ,hτ,hA⟩:= bally hG hK hp Q hQ hQ' he
    have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hv.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
    obtain ⟨u,hU⟩:= posters s (ThroughLaunch.bearing s T) ho
    obtain ⟨O⟩:= Next.Rank.exists_budget G
    refine ⟨s,T,Y,K',hs,hv, τ ⊔ u,hτ.trans le_sup_left,fun k hk =>?_⟩
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
    refine ⟨θ,hθ,fun Ht J T0=>?_⟩; obtain ⟨V,hV,hW⟩:= hB Ht J T0
    refine ⟨V,hV,fun V' hv D W=>?_⟩; obtain ⟨Z,hZ,hW⟩:= hW V' hv D W
    obtain ⟨J',hd,hL,hK,H⟩:= sponsored hG M.K O (Next.Foundations.chart G) (Next.Foundations.chart_ok G) _ hz (fun i=>(hL i).trans (P.large i).need) Z
    refine ⟨J',⟨hZ.1.trans hL,hZ.2.1.trans hd,hZ.2.2.trans hK⟩,fun W ha hb hc a h hi=>?_⟩
    obtain ⟨T',B,hF,R,hR,b,T'',t,Xf,G,hX,hq,hπ⟩:= hW W (hL.trans ha) (hK.trans hb) (hd.trans hc) a h hi
    refine ⟨T',B,hF,R,hR,b,T'',t,Xf,G,hX,hq,?_⟩; intro C; refine ⟨hπ,?_⟩
    obtain ⟨hC,hM,hA,hS,hL₀,S',hA,hC,h₃⟩:= hX.reception
    have hp:= Next.Rank.East.enclosing Xf hX.freight hM
    exact H C (retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid) S' hC hM hp _ _ _ _ _ _ G hS
end YM.PhysicalNext.Repeat.Legato
