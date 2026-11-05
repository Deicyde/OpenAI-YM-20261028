import YM.UVExtension.Case.Serenity
import YM.MergeProof.Serenity
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Income
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment

import YM.UVExtension.Wren.Sand
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Filter Function Set Lattice Wilson Pressure RG RG.Supply Input Precision Org
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {s : Sheet G} {O K : MapPrices} {l v : ℕ→ℕ} {D : Rolls (ThroughLaunch.raise s l)}
  {X : Further.StrongStartup.Tariffs} {Θ : Extra.Multi.Scope} {r : Bid.Worth} {u g k : ℕ→ℝ}
  {t w z : Return.Wages} {R : Targets (ThroughLaunch.raise s l) (UVExtension.Case.actualPay s K)} {E : Expenses R}
  {m : ℕ→ℕ→ℕ} {C : Programs s} {B : ℕ→ℕ→Cafe} {bt : Baton G}
variable (hG : G.Simple) (h : UVExtension.Case.Purchased s O K u g k r X Θ v) (h₀ : v ≤ l)
  (hb : Base (ThroughLaunch.raise s l) (UVExtension.Case.actualPay s K) (chart G) C z t m E) (c₁ c₂ c : ℝ) (h₁ : 0<c₁) (h₂ : 0<c₂) (hc : 0<c)
variable {ε : ℝ} (tool: UVExtension.Guild.Tool ε UVExtension.Camp.soft)
include tool hG h h₀ hb h₁ h₂ hc
lemma uv_employeesT (ht : ∀ j i,0≤t j i) (hf : wantFacet s z c₂ l) (hz:wantFacet s z ε l) (hG₀:UVExtension.Guild.Fall (ThroughLaunch.raise s l) (UVExtension.Case.actualPay s K) R l) (hG₁:UVExtension.Roads.Tags.Rents (ThroughLaunch.raise s l) (UVExtension.Case.actualPay s K) R l) (ha : Height.Aptitude (ThroughLaunch.raise s l) (UVExtension.Case.actualPay s K) E l)
    (hY : ∀ j i,StepStages j i → (s.profile i).supportExponent+3 ≤ (E j i).earn ∧ (s.profile i).supportExponent+3 ≤ t j i ∧ (R j i).halo+ 5 ≤ m j i) (hx : ∀ j i, StepStages j i → (E j i).wanting ≤ -(7/16:ℝ)) {u'}
    (R' : Register D E w u') (hy : Concert D w C (UVExtension.Case.actualPay s K) (chart G) B bt) {F : ℕ→ℕ→Postage} (S : Time.Scouts (F:=F)) (hS : Pocket R' S) (E₀ : ℕ→ℕ→Next.Scheduling.Exchange) (ξ : Extra.Multi.Tariff) :
    ∃ (q : ResetPrices) (η : ℕ→ℝ) (P : PostCost D), ∀ θ₀ : ℕ → ℝ, (∀ j, 0 < θ₀ j) → ∃ θ : Protection D, θ.theta ≤ θ₀ ∧
      ∃ p : ℕ→ℕ→JointLoad.Heir.Record, (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) ∧
        ∀ (Q : ℕ → ℕ → JointLoad.Clockwork.Menu) (U : Delays θ), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→JointLoad.Folio.Aux,
          ∃ W : Delays θ, OrderedDelays W ∧ DelayLe U W ∧
          ∀ V, DelayLe W V → ∀ (Z : Bar V) (I : Wait Z) (a : Levels G) (_ : Paid I a),
            Doors.Budget a k r ∧ Extra.Multi.Prepared Θ ξ (localSection G) a ∧ ∃ (hp : Stock.Priced V) (B' : Directed G I (chart G) (UVExtension.Case.actualPay s K) P),
            B'.a = a ∧ Sheltered (C:=C) (B:=B) (Alloy.mk P θ V Z I hp B' : Alloy (UVExtension.Case.provider s K l) D) bt z t m b Q p J R' S c₁ c₂ c E₀ q η ∧ Roof.Pew (s:=ThroughLaunch.raise s l) z t C p m R' (wind Q) V ε ∧ Height.Rich R' ε V ∧ UVExtension.Guild.Paperwork R' ε UVExtension.Camp.soft V ∧ UVExtension.Roads.Tags.Tax R' V ∧ Planned.Port.AtTop B'.kin ∧ (∀ N, Start.Allows B'.a N) ∧ UVExtension.Free.Report B'.M (UVExtension.Case.actualPay s K) ∧ UVExtension.Reward.Ends B'.a B'.kin.path B'.kin.alpha ∧ ∃ f,RankCovariance.ShapePort B'.a B'.M f:= by
  obtain ⟨q,η,P,hP⟩:= Repeat.uv_commissioning hG h h₀ hb c hc R' hy S hS E₀ ξ (fun _ _=>1/4) (fun _ _=>by norm_num)
  refine ⟨q,η,P,fun θ₀ hθ=>?_⟩; obtain ⟨θ,hθ,p,hp,hF⟩:= hP θ₀ hθ; refine ⟨θ,hθ,p,hp,fun Q U =>?_⟩
  obtain ⟨Tb,hT,hT'⟩:= Opera.conducts U
  obtain ⟨u,hU,hu⟩:= Height.haste R' ha (fun j=>(D.large j).need) Tb
  obtain ⟨w,hw,hw'⟩:= Height.season R' (fun i j h=>lt_of_le_of_lt (hx i j h) (by norm_num)) h₁ u
  obtain ⟨x,hy,hK⟩:= pews (s:=ThroughLaunch.raise s l) z t C p m R' (wind Q) hG h₂ hf hp ht w
  obtain ⟨U₁,hU₁,h₁⟩:= Height.season R' (fun i j h=>lt_of_le_of_lt (hx i j h) (by norm_num)) tool.hr x
  obtain ⟨U₂,hU₂,h₂⟩:= pews (s:=ThroughLaunch.raise s l) z t C p m R' (wind Q) hG tool.hr hz hp ht U₁
  obtain ⟨U₃,hU₃,h₃⟩:= UVExtension.Guild.issues R' tool (fun i j h=> ⟨hx i j h,(hY i j h).1⟩) hG₀ (fun j=>(D.large j).need) U₂
  obtain ⟨U₄,hU₄,h₄⟩:= UVExtension.Roads.Tags.fines R' hG₁ (fun j=>(D.large j).need) U₃
  obtain ⟨b,hb⟩:= hF Q U₄
  refine ⟨b, fun J=>?_⟩; obtain ⟨W,hA,hB,H⟩:=hb J
  refine ⟨W,hA,hT.trans (hU.trans (hw.trans (hy.trans (hU₁.trans (hU₂.trans (hU₃.trans (hU₄.trans hB))))))),fun V hV Z I a ha=>?_⟩
  obtain ⟨hc,hh,hQ,B',ha,hS,hV'⟩:=H V hV Z I a ha; have hZ₄:=hB.trans hV; have hZ₃:=hU₄.trans hZ₄; have hZ₂:=hU₃.trans hZ₃; have hZ₁:=hU₂.trans hZ₂; have hZ:=hU₁.trans hZ₁
  exact ⟨hc,hh,hQ,B',ha,⟨hS,hY,hT' _ (hU.trans (hw.trans (hy.trans hZ))),hK _ hZ,hw' _ (hy.trans hZ),hu _ (hw.trans (hy.trans hZ))⟩, h₂ _ hZ₂,h₁ _ hZ₁,h₃ _ hZ₃,h₄ _ hZ₄,hV'⟩

omit h₀ hb
lemma uv_timberT : ∃ (j : ℕ→ℕ) (C : Programs s) (z : Return.Wages) (R:Targets s (UVExtension.Case.actualPay s K)) (E : Expenses R) (bt : Baton G), v ≤ j ∧
    (∀ i k,(R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=rays s i k ∧ (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0) ∧ ∀ l : ℕ → ℕ,j≤l → Nonempty (Rolls (ThroughLaunch.raise s l)) ∧ ∀ D : Rolls (ThroughLaunch.raise s l),
      ∃ y : Return.Wages, ∀ w : Return.Wages,y≤w → ∃ (u' : ℕ→ℝ) (R' : Register D E w u') (B:ℕ→ℕ→Cafe), ∀ K' : ℕ→ℕ→Postage,
        ∃ (F : ℕ→ℕ→Postage) (S : Time.Scouts (F:=F)), (∀ i j, (F i j).rate ≤ (K' i j).rate) ∧ ∀ (E₀ : ℕ→ℕ→Next.Scheduling.Exchange) (ξ : Extra.Multi.Tariff),
          ∃ (q : ResetPrices) (η : ℕ→ℝ) (P : PostCost D), ∀ θ₀ : ℕ → ℝ, (∀ j, 0 < θ₀ j) → ∃ θ : Protection D, θ.theta ≤ θ₀ ∧
           ∃ p : ℕ→ℕ→JointLoad.Heir.Record, (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) ∧
             ∀ (Q : ℕ → ℕ → JointLoad.Clockwork.Menu) (U : Delays θ), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→JointLoad.Folio.Aux,
               ∃ W : Delays θ, OrderedDelays W ∧ DelayLe U W ∧
               ∀ V, DelayLe W V → ∀ (Z : Bar V) (I : Wait Z) (a : Levels G) (_ : Paid I a),
                 Doors.Budget a k r ∧ Extra.Multi.Prepared Θ ξ (localSection G) a ∧ ∃ (hp : Stock.Priced V) (B' : Directed G I (chart G) (UVExtension.Case.actualPay s K) P),
                 B'.a = a ∧ Sheltered (C:=C) (B:=B) (Alloy.mk P θ V Z I hp B' : Alloy (UVExtension.Case.provider s K l) D) bt z (rays s) mile b Q p J R' S c₁ c₂ c E₀ q η ∧ Roof.Pew (s:=ThroughLaunch.raise s l) z (rays s) C p mile R' (wind Q) V ε ∧ Height.Rich R' ε V ∧ UVExtension.Guild.Paperwork R' ε UVExtension.Camp.soft V ∧ UVExtension.Roads.Tags.Tax R' V ∧ Planned.Port.AtTop B'.kin ∧ (∀ N, Start.Allows B'.a N) ∧ UVExtension.Free.Report B'.M (UVExtension.Case.actualPay s K) ∧ UVExtension.Reward.Ends B'.a B'.kin.path B'.kin.alpha ∧ ∃ f,RankCovariance.ShapePort B'.a B'.M f:= by
  have ht j i:0≤ rays s j i:=by unfold rays; linarith [(s.profile i).price_pos]
  obtain ⟨j,C,z,R,E,hv,hU,hL⟩:= budgets s (UVExtension.Case.actualPay s K) (chart_ok G) mile (rays s) (fun _ _=>-(7/16)) 0 ht (fun _ _=> by norm_num) 500 le_rfl
  obtain ⟨k,hK⟩:= Height.beneath s (UVExtension.Case.actualPay s K) E; obtain ⟨bt⟩:= Psalm.baton_exists G
  obtain ⟨x,hx⟩:= faceting s z h₂
  obtain ⟨c',hc'⟩:= faceting s z tool.hr
  obtain ⟨F,hF⟩:= UVExtension.Guild.fallsStart s _ R
  obtain ⟨G',hg⟩:= UVExtension.Roads.Tags.salts s _ R
  refine ⟨v⊔(((c'⊔F)⊔G')⊔(j⊔(k⊔x))),C,z,R,E,bt,le_sup_left,hU,fun l hl=> ⟨Rolls.exists_rolls _ hG,fun D=>?_⟩⟩
  obtain ⟨hy,hj⟩ := sup_le_iff.mp hl; obtain ⟨hl,hj⟩:=sup_le_iff.mp hj; obtain ⟨hT,hg'⟩:=sup_le_iff.mp hl; obtain ⟨hV,hΩ⟩:=sup_le_iff.mp hT; obtain ⟨hv,hJ⟩:=sup_le_iff.mp hj; obtain ⟨hu,he⟩:=sup_le_iff.mp hJ
  obtain ⟨Y,hY⟩:= (hL l hv).width D bt; refine ⟨Y,fun w hw=>?_⟩; obtain ⟨u,⟨K⟩,c',hY⟩:=hY w hw
  refine ⟨u,K,c',fun K'=>?_⟩; obtain ⟨F,S,hS,H⟩:= pockets K K'
  exact ⟨F,S,hS,fun E₀ ξ=> uv_employeesT hG h hy (hL l hv) c₁ c₂ c h₁ h₂ hc tool ht (fun i j L h h' =>hx _ _ L h ((he j).trans h')) (fun i j L h h'=> hc' _ _ _ h ((hV _).trans h')) (fun i j he B hY=> hF i j he B ((hΩ i).trans hY)) (fun i j he B hY=> hg i j he B ((hg' i).trans hY)) (fun j i h L h' => hK j i h L ((hu j).trans h')) (fun j i _=> ⟨(hU j i).2.2.1.ge,le_rfl,by rw [(hU j i).2.1]⟩) (fun j i _=>by rw [(hU j i).2.2.2.1]) K hY S H E₀ ξ⟩
end YM.PhysicalNext.Repeat.Roof
