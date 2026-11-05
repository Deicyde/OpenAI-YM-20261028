import YM.UVExtension.Case.Trading
import YM.Further.FREE_COVARIANCE_KP.KP.Ride
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Select
import YM.MergeProof.Groom
import YM.MergeProof.North.Tibetan
import YM.MergeProof.Trading
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Orchestral
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Current
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.RibbonRise
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.Ordered
import YM.SectorNext.RECONNECTED_LOCALITY.Deal


/-!
 # Extra purchases, maintaining viability (including pre-L choices). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple) {K : KernelChoices} (hK : ∀ p:Patch,p.Branches K G)
    (v : ThroughLaunch.Orders) (h : ThroughLaunch.Draft v)

section
variable {s: Sheet G} {r:Bid.Worth}{O T : MapPrices} {p h k :ℕ→ℝ} {v₀:ℕ →ℕ}
   {f : Tariffs} {t:Extra.Multi.Scope}(hh : UVExtension.Case.Purchased s O T p h k r f t v₀) (hC : Chop s k mile)
include hh hC hG
lemma uv_expenders (PB:ℕ→ℕ): ∃ f : ℕ → ℕ, v₀ ≤ f ∧ ∀ L :ℕ→ℕ,f ≤ L → Nonempty (Rolls (ThroughLaunch.raise s L)) ∧
    ∀ D : Rolls (ThroughLaunch.raise s L),∃ v: Return.Wages, ∀ w: Return.Wages,v ≤ w→∀ (Q: ℕ→ℕ→Postage)(E : ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff), ∃ (P:PostCost D), ∀ θ₀ : ℕ→ℝ, (∀ i,0<θ₀ i) → ∃ θ:Protection D, θ.theta ≤ θ₀ ∧ ∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu) (T0: Delays θ)(J:ℕ→ℕ→JointLoad.Folio.Aux), ∃ V:Delays θ, DelayLe T0 V∧ OrderedDelays V ∧
      ∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I: Wait b)(a: Levels G)(_ : Paid I a), AsDivisors a.S→ ∃ (hp:Stock.Priced Y) (B: Directed G I (chart G) (UVExtension.Case.actualPay s T) P), let A := (Alloy.mk P θ Y b I hp B : Alloy (UVExtension.Case.provider s T L) D); B.a=a∧Extra.Multi.Prepared t ξ (localSection G) a ∧ ∃ R:Roost.Factor A, R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤ (Q j i).rate) ∧ R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R k r) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ Nonempty (UVExtension.Spire.Grove R) ∧ UVExtension.Roads.Tags.Tax R.shape Y ∧ UVExtension.Free.Report B.M (UVExtension.Case.actualPay s T) ∧ UVExtension.Reward.Ends B.a B.kin.path B.kin.alpha ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
  obtain ⟨ε,hε⟩:= UVExtension.Guild.tooling _ (show 0<UVExtension.Camp.soft from (by norm_num [UVExtension.Camp.soft,UVExtension.Oriel.rim]))
  obtain ⟨f,C,z,R,E,bt,hr,hF,hQ⟩:=uv_commerce hG hh hε
  obtain ⟨n,hA⟩:= Mallow.yearEnd R E
  obtain ⟨L,hM⟩:= Graces.correspond C mile (UVExtension.Case.actualPay s T)
  obtain ⟨T',C',v,hB⟩:= pose s (UVExtension.Case.actualPay s T)
  obtain ⟨π,hπ⟩:= Mallow.harpo s mile
  refine ⟨(f⊔(n⊔(L⊔v)))⊔π, hr.trans (le_sup_left.trans le_sup_left), fun l he=>?_⟩
  obtain ⟨he,hm⟩:=sup_le_iff.mp he
  obtain ⟨hf,hb⟩:=sup_le_iff.mp he; obtain ⟨hn,hv⟩:=sup_le_iff.mp hb; obtain ⟨hl,hv⟩:=sup_le_iff.mp hv
  obtain ⟨h',hp⟩:= hQ _ hf; refine ⟨h',fun D=>?_⟩; obtain ⟨w,H⟩:= hp D
  refine ⟨w,fun w' hw Q E' ξ=>?_⟩
  obtain ⟨u,Z,B,hU⟩:= H w' hw; obtain ⟨F,S,hΨ,hZ⟩:= hU Q
  obtain ⟨q,η,P,hp⟩:=hZ E' ξ; refine ⟨P,fun θ₀ hθ=>?_⟩
  obtain ⟨θ,hα,p₁,hϑ,hK⟩:= hp _ hθ
  obtain ⟨M,hP,H⟩:=cymbals D (retune (u:=l) hB) hv (fun _ _=> 1/4) (fun _ _=> by norm_num)
  refine ⟨θ,hα,fun X V J=>?_⟩
  obtain ⟨V₁,hv₁,hP₁⟩:= Mallow.brevity Z (show Mallow.Arena (ThroughLaunch.raise s l) _ _ _ n from hA) (fun j=>(hn j).trans (D.large j).need) V
  obtain ⟨V₂,hv₂,hP₂⟩:= Graces.reacts (s:=ThroughLaunch.raise s l) C D p₁ mile Z V₁ hϑ
  obtain ⟨V₃,hv₃,hP₃⟩:= Circlet.chords (M:=ThroughLaunch.raise s l) C' D M mile Z hP V₂
  obtain ⟨V₄,hv₄,hP₄⟩:= H θ V₃
  obtain ⟨V₅,hv₅,hP₅⟩:= Graces.compass Z V₄
  obtain ⟨V₆,hv₆,hP₆⟩:= Cub.motions (M:=ThroughLaunch.raise s l) R E mile D Z C' M hP V₅
  obtain ⟨v₇,hv₇,H₇⟩:= Mallow.scarce Z PB V₆
  obtain ⟨v₈,h₈,H₈⟩:= Mallow.swelling Z PB v₇
  obtain ⟨v₉,h₉,H₉⟩:= UVExtension.Above.charts v₈ (show 0<UVExtension.Camp.soft from (by norm_num [UVExtension.Camp.soft,UVExtension.Oriel.rim]))
  obtain ⟨m,Hm⟩:= (UVExtension.Camp.delayed G hG).exists
  let w₀:Delays θ:= { v₉ with betaEntry:=fun i=>max (v₉.betaEntry i) m }
  have h₀: DelayLe v₉ w₀:= ⟨fun _=> le_max_left ..,le_rfl,le_rfl,le_rfl⟩
  obtain ⟨b,hv⟩:= hK X w₀; obtain ⟨W,hO,hQ,hX⟩:=hv J
  refine ⟨W, hv₁.trans (hv₂.trans (hv₃.trans (hv₄.trans (hv₅.trans (hv₆.trans (hv₇.trans (h₈.trans (h₉.trans (h₀.trans hQ))))))))), hO,fun Y he K I a ha hp=>?_⟩
  obtain ⟨hc,hD,hp',B0,hB',hf,hW,hU,hV,hσ⟩:= hX Y he K I a ha
  let A:Alloy (UVExtension.Case.provider s T l) D:= Alloy.mk P θ Y K I hp' B0
  have hg:=hQ.trans he; have hM₉:=h₀.trans hg; have hM₈:=h₉.trans hM₉; have hM₇:= h₈.trans hM₈; have hM₆ := hv₇.trans hM₇; have hM₅:= hv₆.trans hM₆; have hM₄:=hv₅.trans hM₅; have hM₃:=hv₄.trans hM₄
  obtain ⟨V,W,k,hq,hS,ha',hmT⟩:= hσ
  let F' : Factor A:=⟨E',F,S,η,q,w',B,R,E,u,Z,bt,z,rays s,mile,b,C,X,p₁,J,hf,fun i j=> (hF i j).1,hW,hB'.symm ▸ hp⟩
  have hA: m ≤ a.clock.bar:= by rw [ha.bar]; exact ((le_max_right _ _).trans (hg.beta _)).trans K.ready
  have hY:=UVExtension.Above.earned ha (H₉ Y hM₉) hG
  have ht':∀ i, UVExtension.Above.Entry B0.a i UVExtension.Camp.soft:= by rw [hB']; exact hY
  have hk: UVExtension.Guild.Paperwork F'.shape ε UVExtension.Camp.soft A.delay:= k
  refine ⟨hp',B0,hB',hD,F' ,rfl,rfl,hΨ,rfl,rfl,⟨⟨T',C',M,_, retune (u:=l) hB, hP₄ _ hM₄, hP₃ _ hM₃,hP₆ _ hM₆,hP₁ _ (hv₂.trans (hv₃.trans hM₃)),hC,hB'.symm ▸ hc,hP₅ _ hM₅,fun j i d hk f hx=> hM _ _ _ hk f ((hl _).trans hx),hP₂ _ (hv₃.trans hM₃)⟩⟩,H₇ Y hM₇,hπ l hm D,H₈ Y hM₈,⟨ε,UVExtension.Guild.purchase hk V W,k,hS,ha',ht', (show UVExtension.Camp.Fees B0.a from hB' ▸ Hm a hA)⟩,hq,hmT⟩

end
-- Exact continuity of choices returned.
include hG hK h
lemma uv_ruese (PB:ℕ→ℕ): ∃ s:Sheet G,∃ (T:MapPrices) (p: ℕ→ℝ)(W:Bid.Worth), s.kernel=K∧ ThroughLaunch.WithStage s v ∧ ∀ (_f:Tariffs)(X: Extra.Multi.Scope),∃ v: ℕ→ℕ, s.floorL ≤ v ∧
      ∀ k:ℕ→ℕ,v≤k→ Nonempty (Rolls (ThroughLaunch.raise s k))∧ ∀ D: Rolls (ThroughLaunch.raise s k), ∃ v : Return.Wages,∀ w:Return.Wages,v≤w→∀ (Q:ℕ→ℕ→ Postage)(E:ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff),∃ P: PostCost D,
      ∀ θ₀ : ℕ→ℝ,(∀ i,0<θ₀ i)→∃ θ: Protection D,θ.theta ≤ θ₀∧∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu)(J:ℕ→ℕ→JointLoad.Folio.Aux)(T0:Delays θ),∃ V:Delays θ,DelayLe T0 V ∧ OrderedDelays V∧∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I:Wait b)(a:Levels G)(_ : Paid I a),AsDivisors a.S →∃ (hp: Stock.Priced Y) (B: Directed G I (chart G) (UVExtension.Case.actualPay s T) P),let A := (Alloy.mk P θ Y b I hp B : Alloy (UVExtension.Case.provider s T k) D); B.a=a∧ Extra.Multi.Prepared X ξ (localSection G) a ∧∃ R:Factor A,R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤(Q j i).rate)∧R.menu=H∧ R.auxiliary=J ∧ Nonempty (Bandage R p W) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ Nonempty (UVExtension.Spire.Grove R) ∧ UVExtension.Roads.Tags.Tax R.shape Y ∧ UVExtension.Free.Report B.M (UVExtension.Case.actualPay s T) ∧ UVExtension.Reward.Ends B.a B.kin.path B.kin.alpha ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
    obtain ⟨p,hp,h'⟩:= loch mile K h G
    obtain ⟨s,O,T,t,g,W,hS,hW,H⟩:= UVExtension.Case.sailsV hG hK h p hp
    refine ⟨s,T,p,W,hS,hW, fun f X=> ?_⟩
    obtain ⟨v,h⟩:= H f X
    obtain ⟨n,hn,hN⟩:= uv_expenders hG h (h' s hS hW) PB
    refine ⟨n,h.liftL.trans hn, fun k hk=> ⟨(hN k hk).1,fun D=> ?_⟩⟩
    obtain ⟨y,hy⟩:= (hN k hk).2 D; refine ⟨y,fun w hw Q E ξ=>?_⟩; obtain ⟨P,hP⟩:= hy w hw Q E ξ; refine ⟨P,fun θ₀ h₀=> ?_⟩; obtain ⟨θ,hα,hH⟩:= hP θ₀ h₀; exact ⟨θ,hα,fun H J T0 => hH H T0 J⟩

end YM.PhysicalNext.Repeat.Legato
