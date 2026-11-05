import YM.R2I.Wind.Chimes
import YM.R2I.Buckram.Drapes
import YM.FullVolume.Fares.Arc
import YM.RG12.Shadows.Grid
import YM.RG12.Spins.WildPad
import YM.TraceExtension.Made.Exp

/-!
# Pay the Run, Decal and Trace requests simultaneously

Specialize neither `july`, nor `fashions`, nor `Trace.Target.main`. Build
ONCE, buying the extra *before-L* facilities for f756-type Decals, which may
be tuples (pieces can be peeled later). Leave the usual parameters universal
(e.g. can later add post-L price and delay requirements). Adapted from
FullVolume/Fares/Arc, RG12/Shadows/Grid and TraceExtension/Made/Exp.
Not purchasing a UVExtension.Couture: the UV constructor is FullVolume;
one must use the local estimates that don't require a Spire.Uses, or supply
adapters for those layers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.R2I
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple) {K : KernelChoices} (hK : ∀ p:Patch,p.Branches K G)
    (v : ThroughLaunch.Orders) (h : ThroughLaunch.Draft v)

/-- For extending the trace, local/RG12 and source routes without moving to a
new trajectory. `factor` is the honest Run kit. -/
structure Extras (Δ : Daisy.Charity.RG12.Decal G)
    {M : Metals G} {P : Rolls M.p} {A : Alloy M P}
    {K : Roost.Factor A} {y W} (b : Bandage K y W) : Prop where
  tailor : Mallow.RG12.Earned Δ K.shape A.delay
  eight : Pads8 _ b.prices b.teller b.memberB K.span (1/8) A.delay
  nine : Circlet.Pads9 b.prices P b.memberB K.shape A.delay
  soaring : raft P (M:=M) 2 A.delay
  fine : Roof.PriceD K.v K.t K.prices K.recordP K.span K.shape (Roof.wind K.menu) A.delay (1/128)
  treasury : Roof.Vale.ReserveW P K.shape A.post K.scout A.delay
  rollover : WindFare P A.delay
  tracing : Quince.Skill b (Quince.bear W)

section
variable {s: Sheet G} {r:Bid.Worth}{O T : MapPrices} {p h k :ℕ→ℝ} {v₀:ℕ →ℕ}
   {f : Tariffs} {t:Extra.Multi.Scope}(hh : ThroughLaunch.Perceived s O T p h k r f t v₀) (hC : Chop s k mile)
include hh hC hG
lemma joinExpensesShip {ξq ωt ωv:ℝ} (hu:Jams.sphere ξq ωv ωt) (Θ₁:Luna.Tableau ξq 300) (PB:ℕ→ℕ) (Δ : Daisy.Charity.RG12.Decal G): ∃ f : ℕ → ℕ, v₀ ≤ f ∧ ∀ L :ℕ→ℕ,f ≤ L → Nonempty (Rolls (ThroughLaunch.raise s L)) ∧
    ∀ D : Rolls (ThroughLaunch.raise s L),∃ v: Return.Wages, ∀ w: Return.Wages,v ≤ w→∀ (Q: ℕ→ℕ→Postage)(E : ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff), ∃ (P:PostCost D), ∀ θ₀ : ℕ→ℝ, (∀ i,0<θ₀ i) → ∃ θ:Protection D, θ.theta ≤ θ₀ ∧ ∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu) (T0: Delays θ)(J:ℕ→ℕ→JointLoad.Folio.Aux), ∃ V:Delays θ, DelayLe T0 V∧ OrderedDelays V ∧
      ∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I: Wait b)(a: Levels G)(_ : Paid I a), AsDivisors a.S→ ∃ (hp:Stock.Priced Y) (B: Directed G I (chart G) (ThroughLaunch.raging s T) P), let A := (Alloy.mk P θ Y b I hp B : Alloy (ThroughLaunch.bountyV s T L) D); B.a=a∧Extra.Multi.Prepared t ξ (localSection G) a ∧ ∃ R:Roost.Factor A, R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤ (Q j i).rate) ∧ R.menu=H∧ R.auxiliary=J ∧ (∃ b:Bandage R k r, Extras Δ b) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ Jams.Degree R.shape R.scout A.delay ∧ Jams.Savvy R.scout R.target A.delay ξq ωv ωv ωt ∧ Roof.Roofing R ωt ωt ∧ Planned.Port.AtTop B.kin ∧ Stationary.Artes.Cadre P B.kin ∧ Next.Free.Amplify B.M ∧ Jams.PaysW R.shape ωv Y ∧ Luna.Spire Θ₁ R.shape (Luna.costP (ThroughLaunch.raise s L) D) Y ∧ (∃ Xw1, YM.FullVolume.Paint.Tower.Sav G s.profile k Θ₁ Xw1 D.L ∧ Mallow.Canyon ξq R.shape k Θ₁ Xw1 Y) ∧ Jams.Wild R.shape Y ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
  obtain ⟨f,C,z,R,E,bt,hr,hF,hQ⟩:=companyK hG hh hu.1
  obtain ⟨f11,hf11⟩:= Roof.faceting s z (by norm_num : (0:ℝ)<1/128)
  obtain ⟨n10,hA10⟩ := Mallow.RG12.lint Δ R E
  obtain ⟨n,hA⟩:= Mallow.yearEnd R E
  obtain ⟨L,hM⟩:= Graces.correspond C mile (ThroughLaunch.raging s T)
  obtain ⟨T',C',v,hB⟩:= pose s (ThroughLaunch.raging s T)
  obtain ⟨π,hπ⟩:= Mallow.harpo s mile
  obtain ⟨χ,hχ⟩:=Jams.requirements R (fun j i=> by have h₁:=(E j i).worth; rw [(hF j i).2.2.1] at h₁; unfold rays at h₁; linarith [(E j i).first,(E j i).second]) (fun i j=>by have h₁:=(E i j).reach; rw [(hF i j).2.2.2.1] at h₁; exact h₁.le)
  obtain ⟨ϵ,hϵ⟩:=Jams.herds R (fun j i=> by have h₁:=(E j i).worth; rw [(hF j i).2.2.1] at h₁; unfold rays at h₁; linarith [(E j i).first,(E j i).second])
  obtain ⟨γ1,hγ1⟩:=Jams.incomesW R (fun j i=> by have h₁:=(E j i).worth; rw [(hF j i).2.2.1] at h₁; unfold rays at h₁; linarith [(E j i).first,(E j i).second]) (fun i j=>by have h₁:=(E i j).reach; rw [(hF i j).2.2.2.1] at h₁; exact h₁.le)
  obtain ⟨UΩ,YΩ,hQY⟩:= YM.FullVolume.Paint.Tower.require G s.profile k Θ₁
  refine ⟨(f⊔((n ⊔ (n10 ⊔ f11))⊔(L⊔v)))⊔(π⊔χ⊔ϵ ⊔ γ1 ⊔ YΩ), hr.trans (le_sup_left.trans le_sup_left), fun l he=>?_⟩
  obtain ⟨he,hm⟩:=sup_le_iff.mp he
  obtain ⟨hm,hYΩ⟩:= sup_le_iff.mp hm
  obtain ⟨hm,hγ'⟩:= sup_le_iff.mp hm
  obtain ⟨hm,hϵ'⟩:= sup_le_iff.mp hm
  obtain ⟨hm,hχ'⟩:= sup_le_iff.mp hm
  obtain ⟨hf,hb⟩:=sup_le_iff.mp he; obtain ⟨hn,hv⟩:=sup_le_iff.mp hb; obtain ⟨hn,hn10⟩ := sup_le_iff.mp hn; obtain ⟨hl,hv⟩:=sup_le_iff.mp hv
  obtain ⟨hn10,hα11⟩:= sup_le_iff.mp hn10
  obtain ⟨h',hp⟩:= hQ _ hf; refine ⟨h',fun D=>?_⟩; obtain ⟨w,H⟩:= hp D
  refine ⟨w,fun w' hw Q E' ξ=>?_⟩
  obtain ⟨u,Z,B,hU⟩:= H w' hw; obtain ⟨F,S,hΨ,hPocket,hZ⟩:= hU Q
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
  obtain ⟨jA,hjA,huA⟩:= Jams.degrees Z v₈ (fun i j ht=> hχ j i ht _ ((hχ' j).trans (D.large j).need)) hPocket
  obtain ⟨jB,hjB,huB⟩:= Jams.scraps S (R:= (show Targets (ThroughLaunch.raise s l) (ThroughLaunch.raging s T) from R)) hG jA hu (le_refl ωv)
  obtain ⟨jY,hjy,hYx⟩:= Jams.supplies Z jB (fun i j ht=> hϵ j i ht _ ((hϵ' j).trans (D.large j).need) _)
  obtain ⟨uB,hΩ,HΩ⟩:= Jams.donate Z jY (fun i j ht=>hγ1 _ _ ht _ ((hγ' j).trans (D.large j).need)) ωv hu.2.2.1 hu.2.2.2.1
  obtain ⟨uT,hΩ',HΩ'⟩:= Luna.ernes Θ₁ Z _ (fun j i ht d h=>Luna.costGood _ D j i d) uB -- order edit
  obtain ⟨uZ,hψ,Hψ⟩:= Mallow.voyage ξq Z k Θ₁ UΩ uT
  obtain ⟨w₁,hV₁,hw₁⟩:= waves8 uZ (M:=ThroughLaunch.bountyV s T l) (D:=D) (R:=M) (b:=mile) hG (retune (u:=l) hB) (ε:=1/8) (by norm_num)
  obtain ⟨w₂,hV₂,hw₂⟩:= Circlet.tunes9 (M:=ThroughLaunch.raise s l) C' D M Z w₁ hP
  obtain ⟨w₃,hV₃,hw₃⟩:= Mallow.RG12.board Δ Z (show Mallow.RG12.First Δ (ThroughLaunch.raise s l) _ _ _ n10 from hA10) (fun i=> (hn10 i).trans (D.large i).need) (fun i j _=> (hF i j).2.2.2.1.le) w₂
  obtain ⟨w₄,hV₄,hw₄⟩:= Legato.soaring (M:=ThroughLaunch.bountyV s T l) D 2 w₃
  obtain ⟨w₅,hV₅,hw₅⟩:= Roof.clothP (s:=ThroughLaunch.raise s l) z (rays s) C p₁ mile Z (wind X) hG (by norm_num : (0:ℝ)<1/128) (fun i j L h hu=> hf11 i j L h ((hα11 j).trans hu)) hϑ (fun j i=> by unfold rays; linarith [(s.profile i).price_pos]) w₄
  obtain ⟨w₆,hV₆,hw₆⟩:= Roof.Vale.edition (X:=ThroughLaunch.bountyV s T l) D Z P S w₅ (fun i j _=>(hF i j).2.2.2.1)
  obtain ⟨u7,h7,hV7⟩ := Roof.windTime D w₆
  obtain ⟨vC,hj0,hc₁⟩:= Quince.parliament Z C' M mile (Quince.bear r) (Quince.bear_pos r) hP u7
  obtain ⟨b,hv⟩:= hK X vC; obtain ⟨W,hO,hZΩ',hX⟩:=hv J
  have hj:= h7.trans hj0
  have hjW := hV₅.trans (hV₆.trans hj)
  have hZ1W := hV₂.trans (hV₃.trans (hV₄.trans (hjW.trans hZΩ')))
  have hZΩ := hV₁.trans hZ1W
  have hQ:=hψ.trans hZΩ
  refine ⟨W, hv₁.trans (hv₂.trans (hv₃.trans (hv₄.trans (hv₅.trans (hv₆.trans (hv₇.trans (h₈.trans (hjA.trans (hjB.trans (hjy.trans (hΩ.trans (hΩ'.trans hQ)))))))))))), hO,fun Y he K I a ha hp=>?_⟩
  obtain ⟨hc,hD,hp',B0,hB',hf,hρ,hT,hBξ,hAξ,hW,hU,hV,hσ⟩:= hX Y he K I a ha
  let A:Alloy (ThroughLaunch.bountyV s T l) D:= Alloy.mk P θ Y K I hp' B0
  have hM₈:=hjA.trans (hjB.trans (hjy.trans ((hΩ.trans (hΩ'.trans hQ)).trans he))); have hM₇:= h₈.trans hM₈; have hM₆ := hv₇.trans hM₇; have hM₅:= hv₆.trans hM₆; have hM₄:=hv₅.trans hM₅; have hM₃:=hv₄.trans hM₄
  refine ⟨hp',B0,hB',hD, ⟨E',F,S,η,q,w',B,R,E,u,Z,bt,z,rays s,mile,b,C,X,p₁,J,hf,fun i j=> (hF i j).1,hW,hB'.symm ▸ hp⟩,rfl,rfl,hΨ,rfl,rfl,⟨⟨T',C',M,_, retune (u:=l) hB, hP₄ _ hM₄, hP₃ _ hM₃,hP₆ _ hM₆,hP₁ _ (hv₂.trans (hv₃.trans hM₃)),hC,hB'.symm ▸ hc,hP₅ _ hM₅,fun j i d hk f hx=> hM _ _ _ hk f ((hl _).trans hx),hP₂ _ (hv₃.trans hM₃)⟩,
    hw₃ Y (hV₄.trans (hjW.trans (hZΩ'.trans he))), hw₁ Y (hZ1W.trans he),
    hw₂ Y (hV₃.trans (hV₄.trans (hjW.trans (hZΩ'.trans he)))),
    hw₄ Y (hjW.trans (hZΩ'.trans he)), hw₅ Y (hV₆.trans (hj.trans (hZΩ'.trans he))), hw₆ Y (hj.trans (hZΩ'.trans he)), hV7 Y (hj0.trans (hZΩ'.trans he)), hc₁ Y (hZΩ'.trans he)⟩,H₇ Y hM₇,hπ l hm D,H₈ Y hM₈,huA _ (hjB.trans (hjy.trans ((hΩ.trans (hΩ'.trans hQ)).trans he))),huB _ (hjy.trans ((hΩ.trans (hΩ'.trans hQ)).trans he)),hρ,hT,hBξ,hAξ,HΩ Y (hΩ'.trans (hQ.trans he)), HΩ' _ (hQ.trans he), ⟨UΩ,hQY D.L (fun j=> (hYΩ j).trans (D.large j).need),Hψ Y (hZΩ.trans he)⟩, hYx Y ((hΩ.trans (hΩ'.trans hQ)).trans he),_,hσ.choose_spec⟩

end
-- Exact continuity of choices returned.
include hG hK h
lemma joinRadarsShip {ξq ωt ωv:ℝ}(hu:Jams.sphere ξq ωv ωt) (Θ₁:Luna.Tableau ξq 300) (PB:ℕ→ℕ) (Δ : Daisy.Charity.RG12.Decal G): ∃ s:Sheet G,∃ (T:MapPrices) (p: ℕ→ℝ)(W:Bid.Worth), s.kernel=K∧ ThroughLaunch.WithStage s v ∧ ∀ (_f:Tariffs)(X: Extra.Multi.Scope),∃ v: ℕ→ℕ, s.floorL ≤ v ∧
      ∀ k:ℕ→ℕ,v≤k→ Nonempty (Rolls (ThroughLaunch.raise s k))∧ ∀ D: Rolls (ThroughLaunch.raise s k), ∃ v : Return.Wages,∀ w:Return.Wages,v≤w→∀ (Q:ℕ→ℕ→ Postage)(E:ℕ→ℕ→Exchange)(ξ:Extra.Multi.Tariff),∃ P: PostCost D,
      ∀ θ₀ : ℕ→ℝ,(∀ i,0<θ₀ i)→∃ θ: Protection D,θ.theta ≤ θ₀∧∀ (H:ℕ→ℕ→JointLoad.Clockwork.Menu)(J:ℕ→ℕ→JointLoad.Folio.Aux)(T0:Delays θ),∃ V:Delays θ,DelayLe T0 V ∧ OrderedDelays V∧∀ Y:Delays θ,DelayLe V Y→∀ (b:Bar Y)(I:Wait b)(a:Levels G)(_ : Paid I a),AsDivisors a.S →∃ (hp: Stock.Priced Y) (B: Directed G I (chart G) (ThroughLaunch.raging s T) P),let A := (Alloy.mk P θ Y b I hp B : Alloy (ThroughLaunch.bountyV s T k) D); B.a=a∧ Extra.Multi.Prepared X ξ (localSection G) a ∧∃ R:Factor A,R.walls=w∧ R.exchange=E ∧ (∀ j i,(R.book j i).rate ≤(Q j i).rate)∧R.menu=H∧ R.auxiliary=J ∧ (∃ b:Bandage R p W, Extras Δ b) ∧ Mallow.Minty R.shape PB Y ∧ (∀ i j,Push.PriceCompiler.StepStages i j→Real.exp (Release.base ((s.profile j).supportExponent+2) (R.span i j)) ≤ (D.L i).val) ∧ Mallow.AccordV R.shape PB Y ∧ Jams.Degree R.shape R.scout A.delay ∧ Jams.Savvy R.scout R.target A.delay ξq ωv ωv ωt ∧ Roof.Roofing R ωt ωt ∧ Planned.Port.AtTop B.kin ∧ Stationary.Artes.Cadre P B.kin ∧ Next.Free.Amplify B.M ∧ Jams.PaysW R.shape ωv Y ∧ Luna.Spire Θ₁ R.shape (Luna.costP (ThroughLaunch.raise s k) D) Y ∧ (∃ Xw1, YM.FullVolume.Paint.Tower.Sav G s.profile p Θ₁ Xw1 D.L ∧ Mallow.Canyon ξq R.shape p Θ₁ Xw1 Y) ∧ Jams.Wild R.shape Y ∧ ∃ f,RankCovariance.ShapePort B.a B.M f :=by
    obtain ⟨p,hp,h'⟩:= loch mile K h G
    obtain ⟨s,O,T,t,g,W,hS,hW,H⟩:= ThroughLaunch.sailsW hG hK h p hp
    refine ⟨s,T,p,W,hS,hW, fun f X=> ?_⟩
    obtain ⟨v,h⟩:= H f X
    obtain ⟨n,hn,hN⟩:= joinExpensesShip hG h (h' s hS hW) hu Θ₁ PB Δ
    refine ⟨n,h.liftL.trans hn, fun k hk=> ⟨(hN k hk).1,fun D=> ?_⟩⟩
    obtain ⟨y,hy⟩:= (hN k hk).2 D; refine ⟨y,fun w hw Q E ξ=>?_⟩; obtain ⟨P,hP⟩:= hy w hw Q E ξ; refine ⟨P,fun θ₀ h₀=> ?_⟩; obtain ⟨θ,hα,hH⟩:= hP θ₀ h₀; exact ⟨θ,hα,fun H J T0 => hH H T0 J⟩

end YM.PhysicalNext.Repeat.Legato.R2I

#print axioms YM.PhysicalNext.Repeat.Legato.R2I.joinRadarsShip
