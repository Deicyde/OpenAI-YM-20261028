import YM.FullVolume.Roll.Compass
import YM.FullVolume.Stage.Comm
/- adapt Retreat.lean -/
import YM.MergeProof.Serenity
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Income
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment

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
  {t w z : Return.Wages} {R : Targets (ThroughLaunch.raise s l) (ThroughLaunch.raging s K)} {E : Expenses R}
  {m : ℕ→ℕ→ℕ} {C : Programs s} {B : ℕ→ℕ→Cafe} {bt : Baton G}
variable (hG : G.Simple) (h : ThroughLaunch.Perceived s O K u g k r X Θ v) (h₀ : v ≤ l)
  (hb : Base (ThroughLaunch.raise s l) (ThroughLaunch.raging s K) (chart G) C z t m E) (c₁ c₂ c : ℝ) (h₁ : 0<c₁) (h₂ : 0<c₂) (hc : 0<c)
include hG h h₀ hb h₁ h₂ hc
lemma employeesUK (ht : ∀ j i,0≤t j i) (hf : wantFacet s z c₂ l) (hf': wantFacet s z (1/16) l) (ha : Height.Aptitude (ThroughLaunch.raise s l) (ThroughLaunch.raging s K) E l)
    (hY : ∀ j i,StepStages j i → (s.profile i).supportExponent+3 ≤ (E j i).earn ∧ (s.profile i).supportExponent+3 ≤ t j i ∧ (R j i).halo+ 5 ≤ m j i) (hx : ∀ j i, StepStages j i → (E j i).wanting < -(3/8:ℝ)) {u'}
    (R' : Register D E w u') (hy : Concert D w C (ThroughLaunch.raging s K) (chart G) B bt) {F : ℕ→ℕ→Postage} (S : Time.Scouts (F:=F)) (hS : Pocket R' S) (E₀ : ℕ→ℕ→Next.Scheduling.Exchange) (ξ : Extra.Multi.Tariff) :
    ∃ (q : ResetPrices) (η : ℕ→ℝ) (P : PostCost D), ∀ θ₀ : ℕ → ℝ, (∀ j, 0 < θ₀ j) → ∃ θ : Protection D, θ.theta ≤ θ₀ ∧
      ∃ p : ℕ→ℕ→JointLoad.Heir.Record, (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) ∧
        ∀ (Q : ℕ → ℕ → JointLoad.Clockwork.Menu) (U : Delays θ), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→JointLoad.Folio.Aux,
          ∃ W : Delays θ, OrderedDelays W ∧ DelayLe U W ∧
          ∀ V, DelayLe W V → ∀ (Z : Bar V) (I : Wait Z) (a : Levels G) (_ : Paid I a),
            Doors.Budget a k r ∧ Extra.Multi.Prepared Θ ξ (localSection G) a ∧ ∃ (hp : Stock.Priced V) (B' : Directed G I (chart G) (ThroughLaunch.raging s K) P),
            B'.a = a ∧ Sheltered (C:=C) (B:=B) (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.bountyV s K l) D) bt z t m b Q p J R' S c₁ c₂ c E₀ q η ∧ Sheltered (C:=C) (B:=B) (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.bountyV s K l) D) bt z t m b Q p J R' S (1/16) (1/16) c E₀ q η ∧ Planned.Port.AtTop B'.kin ∧ Stationary.Artes.Cadre P B'.kin ∧ Next.Free.Amplify B'.M ∧ ∃ f,RankCovariance.ShapePort B'.a B'.M f:= by
  obtain ⟨q,η,P,hP⟩:= Repeat.commissionK hG h h₀ hb c hc R' hy S hS E₀ ξ (fun _ _=>1/4) (fun _ _=>by norm_num)
  refine ⟨q,η,P,fun θ₀ hθ=>?_⟩; obtain ⟨θ,hθ,p,hp,hF⟩:= hP θ₀ hθ; refine ⟨θ,hθ,p,hp,fun Q U =>?_⟩
  obtain ⟨Tb,hT,hT'⟩:= Opera.conducts U
  obtain ⟨u,hU,hu⟩:= Height.haste R' ha (fun j=>(D.large j).need) Tb
  obtain ⟨w,hw,hw'⟩:= Height.season R' hx h₁ u
  obtain ⟨x,hy,hK⟩:= pews (s:=ThroughLaunch.raise s l) z t C p m R' (wind Q) hG h₂ hf hp ht w
  obtain ⟨W,hb0,h0⟩:= Height.season R' hx (by norm_num : 0<(1/16:ℝ)) x
  obtain ⟨T,hb1,hk'⟩:= pews (s:=ThroughLaunch.raise s l) z t C p m R' (wind Q) hG (by norm_num: 0<(1/16:ℝ)) hf' hp ht W
  obtain ⟨b,hb⟩:= hF Q T
  refine ⟨b, fun J=>?_⟩; obtain ⟨W,hA,hB,H⟩:=hb J
  refine ⟨W,hA,hT.trans (hU.trans (hw.trans (hy.trans (hb0.trans (hb1.trans hB))))),fun V hV Z I a ha=>?_⟩
  obtain ⟨hc,hh,hQ,B',ha,hS,hV'⟩:=H V hV Z I a ha; have hZ:=hb0.trans (hb1.trans (hB.trans hV))
  exact ⟨hc,hh,hQ,B',ha,⟨hS,hY,hT' _ (hU.trans (hw.trans (hy.trans hZ))),hK _ hZ,hw' _ (hy.trans hZ),hu _ (hw.trans (hy.trans hZ))⟩,⟨hS,hY,hT' _ (hU.trans (hw.trans (hy.trans hZ))),hk' _ (hB.trans hV),h0 _ (hb1.trans (hB.trans hV)),hu _ (hw.trans (hy.trans hZ))⟩,hV'⟩

omit h₀ hb
lemma timberUK : ∃ (j : ℕ→ℕ) (C : Programs s) (z : Return.Wages) (R:Targets s (ThroughLaunch.raging s K)) (E : Expenses R) (bt : Baton G), v ≤ j ∧
    (∀ i k,(R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=rays s i k ∧ (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0) ∧ ∀ l : ℕ → ℕ,j≤l → Nonempty (Rolls (ThroughLaunch.raise s l)) ∧ ∀ D : Rolls (ThroughLaunch.raise s l),
      ∃ y : Return.Wages, ∀ w : Return.Wages,y≤w → ∃ (u' : ℕ→ℝ) (R' : Register D E w u') (B:ℕ→ℕ→Cafe), ∀ K' : ℕ→ℕ→Postage,
        ∃ (F : ℕ→ℕ→Postage) (S : Time.Scouts (F:=F)), (∀ i j, (F i j).rate ≤ (K' i j).rate) ∧ Pocket R' S ∧ ∀ (E₀ : ℕ→ℕ→Next.Scheduling.Exchange) (ξ : Extra.Multi.Tariff),
          ∃ (q : ResetPrices) (η : ℕ→ℝ) (P : PostCost D), ∀ θ₀ : ℕ → ℝ, (∀ j, 0 < θ₀ j) → ∃ θ : Protection D, θ.theta ≤ θ₀ ∧
           ∃ p : ℕ→ℕ→JointLoad.Heir.Record, (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) ∧
             ∀ (Q : ℕ → ℕ → JointLoad.Clockwork.Menu) (U : Delays θ), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→JointLoad.Folio.Aux,
               ∃ W : Delays θ, OrderedDelays W ∧ DelayLe U W ∧
               ∀ V, DelayLe W V → ∀ (Z : Bar V) (I : Wait Z) (a : Levels G) (_ : Paid I a),
                 Doors.Budget a k r ∧ Extra.Multi.Prepared Θ ξ (localSection G) a ∧ ∃ (hp : Stock.Priced V) (B' : Directed G I (chart G) (ThroughLaunch.raging s K) P),
                 B'.a = a ∧ Sheltered (C:=C) (B:=B) (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.bountyV s K l) D) bt z (rays s) mile b Q p J R' S c₁ c₂ c E₀ q η ∧ Sheltered (C:=C) (B:=B) (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.bountyV s K l) D) bt z (rays s) mile b Q p J R' S (1/16) (1/16) c E₀ q η ∧ Planned.Port.AtTop B'.kin ∧ Stationary.Artes.Cadre P B'.kin ∧ Next.Free.Amplify B'.M ∧ ∃ f,RankCovariance.ShapePort B'.a B'.M f:= by
  have ht j i:0≤ rays s j i:=by unfold rays; linarith [(s.profile i).price_pos]
  obtain ⟨j,C,z,R,E,hv,hU,hL⟩:= budgets s (ThroughLaunch.raging s K) (chart_ok G) mile (rays s) (fun _ _=>-(7/16)) 0 ht (fun _ _=> by norm_num) 500 le_rfl
  obtain ⟨k,hK⟩:= Height.beneath s (ThroughLaunch.raging s K) E; obtain ⟨bt⟩:= Psalm.baton_exists G
  obtain ⟨x,hx⟩:= faceting s z h₂
  obtain ⟨x',hx'⟩:=faceting s z (by norm_num: 0<(1/16:ℝ))
  refine ⟨v⊔(j⊔(k⊔(x⊔x'))),C,z,R,E,bt,le_sup_left,hU,fun l hl=> ⟨Rolls.exists_rolls _ hG,fun D=>?_⟩⟩
  obtain ⟨hy,hj⟩ := sup_le_iff.mp hl; obtain ⟨hv,hJ⟩:=sup_le_iff.mp hj; obtain ⟨hu,he⟩:=sup_le_iff.mp hJ
  obtain ⟨he,he'⟩:= sup_le_iff.mp he
  obtain ⟨Y,hY⟩:= (hL l hv).width D bt; refine ⟨Y,fun w hw=>?_⟩; obtain ⟨u,⟨K⟩,c',hY⟩:=hY w hw
  refine ⟨u,K,c',fun K'=>?_⟩; obtain ⟨F,S,hS,H⟩:= pockets K K'
  exact ⟨F,S,hS,H,fun E₀ ξ=> employeesUK hG h hy (hL l hv) c₁ c₂ c h₁ h₂ hc ht (fun i j L h h' =>hx _ _ L h ((he j).trans h')) (fun i j L h h' =>hx' _ _ L h ((he' j).trans h')) (fun j i h L h' => hK j i h L ((hu j).trans h')) (fun j i _=> ⟨(hU j i).2.2.1.ge,le_rfl,by rw [(hU j i).2.1]⟩) (fun j i _=>by rw [(hU j i).2.2.2.1]; norm_num) K hY S H E₀ ξ⟩
end YM.PhysicalNext.Repeat.Roof
