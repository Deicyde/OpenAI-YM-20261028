import YM.SharpGram.Assembly.SameFactory
import YM.SharpGram.Dense.Slender
import YM.SharpGram.Dense.Passes
import YM.UVExtension.Oasis.Wish
import YM.OPE.Log.Plans
import YM.UVExtension.Oasis.Hall

/-!
# Simultaneous choice theorem, retaining UV slack

Collect Witness of UVExtension.Reports.ultraviolet with OPE.Facilities to
keep all comparisons on one common instance. Include TrueSteps upgrade.
Adapted Oasis/Wish.lean and Hall.lean, and OPE/Log/Entrance.lean, using new
joint selection at mark/stage prices.
-/
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
variable (Q2:ℕ→ℕ) (hQ2:Monotone Q2) (hQ2':∀ i,1 ≤ Q2 i)
open SharpGram
include hp hQ2 hQ2' hQ hQ' hK hG
lemma jointOffers (he:∀ i,100 ≤ v.supportExp i): ∃ (s:Sheet G)(T:MapPrices)(P0:ℕ→ℝ)(K':Bid.Worth), s.kernel=K ∧ WithStage s v ∧ ∃ τ:ℕ→ℕ,s.floorL ≤τ ∧ ∀ k:ℕ→ℕ,τ≤k→ let M:= UVExtension.Case.provider s T k; Nonempty (Rolls M.p)∧∀ (P:Rolls M.p), ∃ U:Return.Wages,∀ w:Return.Wages,U≤w→∀ (Qt:ℕ→ℕ→Postage) (E:ℕ→ℕ→Exchange), ∃ F:PostCost P,∀ θ₀:ℕ→ℝ,(∀ i:ℕ,0<θ₀ i)→∃ θ:Protection P,θ.theta≤θ₀ ∧∀ (Ht:ℕ→ℕ→JointLoad.Clockwork.Menu)(J':ℕ→ℕ→ JointLoad.Folio.Aux) (T0:Delays θ),∃ V:Delays θ,DelayLe T0 V∧∀ V':Delays θ,DelayLe V V'→∀ (D:Bar V') (W:Wait D),∃ Z:Wait D,(W.readyHere ≤ Z.readyHere ∧ W.minLength ≤ Z.minLength ∧ W.window ≤ Z.window) ∧ ∀ (W':Wait D), Z.readyHere ≤ W'.readyHere→ Z.window ≤ W'.window→ Z.minLength ≤ W'.minLength→∀ (a:Levels G), Paid W' a → AsDivisors a.S→∃ (h:Stock.Priced V') (B:Directed G W' M.O M.K F),B.a=a∧∃ (X: Factor (Alloy.mk F θ V' D W' h B : Alloy M P)),(X.walls=w∧ X.exchange=E∧ (∀ j i,(X.book j i).rate ≤ (Qt j i).rate)∧ X.menu=Ht∧ X.auxiliary=J')∧∃ (b:Bandage X P0 K'), ∃ T t, ∃ (N: UVExtension.Spire.Uses X hG) (hv:UVExtension.Upland.Arc X N T) (hk:UVExtension.Mast.Lisle t B.a),
 let S:= UVExtension.Mast.cellar N b hv t hk; let Y:= UVExtension.Mast.centerB N hv; let p:= UVExtension.Mast.roseA N
 Chateau b Q Y t (UVExtension.Mast.Cellar.gate p S) (UVExtension.Orchard.roof N p) ∧  Stock.Tabs B.a ∧ Velour (UVExtension.Mast.Cellar.yard p S) (renal B.a) (mutt B.a Q) (UVExtension.Orchard.roof N p) ∧ UVExtension.Harvest.Barn N b Q S∧
 TrueSteps (UVExtension.Mast.Cellar.yard p S) K' ∧   Fridge (UVExtension.Mast.Cellar.yard p S) (far B.a) (fly B.a) ∧   Chateau b Q2 Y t (UVExtension.Mast.Cellar.gate p S) (UVExtension.Orchard.roof N p) ∧   Velour (UVExtension.Mast.Cellar.yard p S) (renal B.a) (mutt B.a Q2) (UVExtension.Orchard.roof N p) ∧   VelourArity (UVExtension.Mast.Cellar.yard p S) (renal B.a) (mutt B.a Q2) (UVExtension.Orchard.roof N p) ∧   LightArity (UVExtension.Mast.Cellar.yard p S) (renal B.a) (mutt B.a Q2) (UVExtension.Orchard.roof N p) ∧ UVExtension.Cloud.Leases P0 X.shape V' ∧ (∀ i j,(X.target i j).rate ≤ -(7/16:ℝ)) ∧ (∃ r:ℝ,0 < r∧ Metric.ball (0:ℂ) r⊆ UVExtension.Camp.Broad a∧∀ d N' n:ℕ,t d ≤ N'→ Nonempty (UVExtension.Gale.Circuit N d N' n b S r)) ∧ ∀ f:Extraction.Order, CompleteWeak (UVExtension.Mast.Cellar.yard p S) f := by
    obtain ⟨s,T,Y,K',hs,hv,τ,hτ,hA⟩:= havens_log hG hK hp Q hQ hQ' Q2 hQ2 hQ2' he
    have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hv.jets]; exact (le_max_right ..).trans (hp.k i)) tendsto_id
    obtain ⟨u,hU⟩:= posters s (UVExtension.Case.actualPay s T) ho
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
    obtain ⟨T',B,hF,R,hR,b,T'',t,N,H0,hk,hX,hq,H',hπ,hTrue,hFr,hX2,hV2,hN2,hL2,hα,hθ⟩:= hW W (hL.trans ha) (hK.trans hb) (hd.trans hc) a h hi
    refine ⟨T',B,hF,R,hR,b,T'',t,N,H0,hk,?_⟩; intro S W p; refine ⟨hX,hq,H',hπ,hTrue,hFr,hX2,hV2,hN2,hL2,hα,hθ,?_,?_⟩
    · obtain ⟨a₁,ht,h,hr⟩:= UVExtension.Gale.sheaf N b hα hθ H0 hk; exact ⟨a₁,ht,hF ▸ h,hr⟩
    let Z:=UVExtension.Mast.Cellar.yard p S
    obtain ⟨hC,hM,hA,hS,hL₀,S',hA,hC,h₃⟩:= hX.reception
    let G:=UVExtension.Orchard.roof N p; let X:= UVExtension.Mast.Cellar.gate p S
    have hp:= Next.Rank.East.enclosing (T:=W) (Y:=X) hX.freight hM
    exact H Z (retains_budget hc (fun i=>⟨ha i,hb i⟩) B.valid) S' hC hM hp _ _ _ _ _ _ G hS

omit hp hQ hQ' hK hQ2 hQ2'
open UVExtension UVExtension.Harvest
/-! price from same schedule, Barn pins together all projections and histories,
    Transfers peak & radiances, see e.g. Poppy.Fountain. Real offset laws
    on `.yard` are the marked families actually tested. At the center exact
    CLOSED acquisitions via UV-stress.Weak L output. -/
include hG
theorem uv_log {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    UVExtension.Oasis.Floral (hG:=hG) C ∧ Acme.Aroma C ∧ (∃ W r D, OPE.Log.LogPackage C W r D ∧ TrueSteps C W) ∧ (∃ h:C.Makes, Dense.Coverage C h) ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= le_rfl
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    exact le_rfl
  obtain ⟨s,T,Y,K,hX,hStage,l,hL,hK⟩:= jointOffers hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl)
      (fun j => j+1) (by intro i j h; exact Nat.add_le_add_right h 1) (fun i => by omega) hE
  have ho:Tendsto (fun i=>(s.profile i).order) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> by rw [hStage.jets]; exact (le_max_right ..).trans (he.k i)) tendsto_id
  obtain ⟨R,hR⟩:= Pert.Dense.bulletin s (UVExtension.Case.actualPay s T) ho
  obtain ⟨O⟩:= Next.Rank.exists_budget G
  let M:=UVExtension.Case.provider s T (l⊔R)
  obtain ⟨⟨P⟩,H⟩:= hK _ (le_sup_left (b:=R))
  -- reflexive stage promotion (as in Pert.Dense.Kernel)
  have hz : Pert.Dense.Relay M.p M.K R:=by
     obtain ⟨b,F,ψ,he,v⟩:= hR.bulletin
     refine ⟨b,F,ψ,he,v.same,?_,?_,?_⟩
     · intro i; exact ⟨(v.buys i).1,(v.buys i).2⟩
     · intro i; exact ⟨(v.shops i).1⟩
     intro i d j;exact v.lifts i d j
  have hUQ :∀ i,R i ≤ (P.L i).val:=fun i=>(le_sup_right (a:=l) (b:=R) i).trans (P.large i).need
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩
  obtain ⟨Ua, -, hHalo⟩ := OPE.halo_delay U
  obtain ⟨Ub,hUD,hw'⟩ := OPE.Log.aux_delay Ua
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ Ub
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y0,-,H⟩:= hK V (DelayLe.refl _) D I
  let W0 : Wait D:= ⟨fun _ => 0,Dense.slim D,Dense.slimWindow hG D,0⟩
  obtain ⟨W2,_,hSlim,WP,hWP⟩ := Pert.Dense.slim_wait_for M.K O (Next.Foundations.chart G) W0 hG hz hUQ (Next.Foundations.chart_ok G) rfl
  obtain ⟨Y,hYT,hLate⟩:= Dense.loadBoth hG Y0 W2
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,Hx,Hk,hT,hq,hu,hD,hTrue,hFr,hX2,hV2,hN2,hL2,h_lease,h_rate,⟨hh',hH,h_Φ,h_sh⟩,hE⟩:= H Y hYT.ready hYT.range hYT.minL a ha hp
  let Vc:= Mast.centerB S Hx; let W:=Mast.cellar S c Hx t Hk; let S':= Mast.Cellar.gate (Mast.roseA S) W
  let Z:= Family.mk (Issue.trail Vc) (hol G) (Labels.frames G) (localSection G) t S'
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,hX₃,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S',rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu hq hv hF,hq, Ribbons.fugacious Z hG hu⟩
  have hCover : Dense.Coverage Z hF := Dense.covered M.K O (Next.Foundations.chart G) WP hWP hSlim hLate B.valid B₀ hX₃ hF (Next.Rank.East.enclosing _ hT.freight hF)
  have huh := hUD.trans h₁
  refine ⟨_,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hc,hF,hW,Oasis.survives W Hx hD hQ hh' hH (hB.symm ▸ h_Φ) h_sh h_lease h_rate hT hu, hπ,?_,⟨hF,hCover⟩,fun f hf=>⟨grilled Z hF hU hq hf,hE f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
  obtain ⟨_,_,_,hScrim,hU2⟩ := hX2.reception
  refine ⟨_, _, _, ⟨⟨⟨hScrim, hV2, fun d N p hn m hm hx => ?_, hFr, ?_, hQ, hv, hq⟩,
    hN2⟩, hL2, hw' V h₁ Y B.a B.valid, ?_, ?_⟩, hTrue⟩
  · exact (hTrue.reads d m N p hm hx).triangle
  · apply hHalo V huh Y B.a B.valid
  · refine tendsto_atTop_mono (f:=B.a.clock.J) (fun i=> ?_) B.a.fits.deep
    change B.a.clock.J i ≤ B.a.clock.J (i+1)+1
    exact (B.a.fits.mono i.le_succ).trans (Nat.le_succ _)
  · intro i; change (B.a.params i).supportExponent=100; rw [params_eq B.valid]; exact hStage.prices _
end YM.PhysicalNext.Repeat.Legato
