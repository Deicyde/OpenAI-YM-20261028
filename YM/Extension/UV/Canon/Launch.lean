import YM.Extension.UV.Canon.Core
import YM.MergeProof.Island
import YM.Next.RANK.Flux.Chronicle
import YM.Next.RANK.Prepaid
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Atlas
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Venue
import YM.Planned.RECIPE_STARTUP_PORT.FreeEdge


set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat
open Filter Function Set Lattice Wilson Pressure RG RG.Supply Input Precision Org
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge.VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {s : Sheet G} {O K : MapPrices} {l v : ℕ→ℕ} {D : Rolls (ThroughLaunch.raise s l)}
  {X : Further.StrongStartup.Tariffs} {Θ : Extra.Multi.Scope} {r : Bid.Worth} {u g k : ℕ→ℝ}
  {t w z : Return.Wages} {R : Targets (ThroughLaunch.raise s l) (ThroughLaunch.bearing s K)} {E : Expenses R}
  {m : ℕ→ℕ→ℕ} {C : Programs s} {B : ℕ→ℕ→Cafe} {bt : Baton G}

-- deploy on ALL even bigger delays. SectionData costs retained for Guard consumers.
variable (hG : G.Simple) (h : ThroughLaunch.PaidView s O K u g k r X Θ v) (h₀ : v ≤ l)
  (hb : Base (ThroughLaunch.raise s l) (ThroughLaunch.bearing s K) (chart G) C z t m E)
  (c : ℝ) (hc : 0<c) {u' : ℕ→ℝ} (R' : Register D E w u') (hy : Concert D w C (ThroughLaunch.bearing s K) (chart G) B bt)

include hG h h₀ hb hc R' hy
lemma commissioningV {F : ℕ→ℕ→Postage} (S : Time.Scouts (F:=F)) (hS : Pocket R' S)
    (E₀ : ℕ→ℕ→Next.Scheduling.Exchange) (ξ : Extra.Multi.Tariff) (cap : Return.Wages) (hk : ∀ j i,0<cap j i) :
    ∃ (q : ResetPrices) (η : ℕ→ℝ) (P : PostCost D), ∀ θ₀ : ℕ → ℝ, (∀ j, 0 < θ₀ j) → ∃ θ : Protection D, θ.theta ≤ θ₀ ∧
      ∃ p : ℕ→ℕ→JointLoad.Heir.Record, (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ cap j i) ∧
        ∀ (Q : ℕ → ℕ → JointLoad.Clockwork.Menu) (U : Delays θ), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→JointLoad.Folio.Aux,
          ∃ W : Delays θ, OrderedDelays W ∧ DelayLe U W ∧
          ∀ V, DelayLe W V → ∀ (Z : Bar V) (I : Wait Z) (a : Levels G) (_ : Paid I a),
            Doors.Budget a k r ∧ Extra.Multi.Prepared Θ ξ (localSection G) a ∧ ∃ (hp : Stock.Priced V) (B' : Directed G I (chart G) (ThroughLaunch.bearing s K) P),
            B'.a = a ∧ Touring (C:=C) (B:=B) (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.currency s K l) D) bt z t m b Q p J R' S c E₀ q η ∧ Extension.UV.Archive B' ∧ ∃ f,RankCovariance.ShapePort B'.a B'.M f := by
  obtain ⟨y,hP,he⟩ := h.ship l h₀ D
  let H i := fromMin (fun i j => (F i j).rate/4) i
  let P : PostCost D := ⟨y,1,g,H,hP.pos,fun _=>zero_lt_one,h.slopePrice,fun i=> lt_min (div_pos (F i i).pos (by norm_num)) (div_pos (F i (i-1)).pos (by norm_num))⟩
  let q : ResetPrices := ⟨fun _ i=>4*Time.credit G (s.profile i),1,fun _ i=> mul_pos (by norm_num) (Time.credit_pos ..),fun _ _=>zero_lt_one,fun _ _=>le_rfl⟩
  obtain ⟨η,hη,Hη⟩ := Time.beforeWait (s:=ThroughLaunch.raise s l) hG
  refine ⟨q,η,P,fun θ₀ hq=>?_⟩
  obtain ⟨θ,hθ⟩ := Protection.exists_margin D (fun j=> min 1 (θ₀ j)) (fun j=> lt_min one_pos (hq j))
  obtain ⟨p,hp,hD⟩ := hy.endures (P:=θ) hb.paid (chart_ok _) _ hk
  refine ⟨θ,fun i=> (hθ i).trans (min_le_right ..),p,hp,fun Q U=>?_⟩
  obtain ⟨V,hU,hW⟩ := hS.booked hb.floors (fun i=>(D.large i).need) U hc
  obtain ⟨V',hv,_,_,_,-,hv'⟩ := he P rfl le_rfl le_rfl θ ξ 0 le_rfl V
  obtain ⟨V₀,hy,hy'⟩ := Hη D θ q z F F P S 0 (fun i=>(hθ i).trans (min_le_left ..)) hb.paid.pre (fun _ _ _ => tendsto_const_nhds) V'
  obtain ⟨b,hb'⟩ := hD Q V₀
  refine ⟨b,fun J => ?_⟩
  obtain ⟨Y,hY,hM,hK⟩ := hb' J
  refine ⟨Y,hY,hU.trans ((fromBoost hv).trans ((fromBoost hy).trans hM)), fun L hB Z I a ha =>?_⟩
  obtain ⟨ht,hx,-,-,he⟩ := hv' _ (hy.chain (asBoost (hM.trans hB)))
  obtain ⟨hc,hh,M,k,hT⟩ := he Z I a ha
  obtain ⟨hhp,hS⟩ := hK L hB
  obtain ⟨hm,hN,hg,hL⟩ := hy' L (asBoost (hM.trans hB))
  obtain ⟨hr,hE⟩ := hhp.plan.priors
  have H (i j : ℕ) (hj : StepStages i j) : P.g i ≤ (F i j).rate/4 ∧ Time.credit G (s.profile j) ≤ q.cost i j/4 :=
    ⟨fromMin_le (fun i j => (F i j).rate/4) hj, show _ ≤ (4*Time.credit G (s.profile j))/4 by linarith⟩
  have he := Service.depT hG ha hT ht hx hm H hN hg (hL Z I a ha) hr hE E₀
  refine ⟨hc,hh,hx,_,rfl,⟨hhp,hS,he.ff,he.boot,?_,hW _ ((fromBoost hv).trans ((fromBoost hy).trans (hM.trans hB)))⟩, Extension.UV.Archive.pack hT ha (fun i=> (Further.StrongStartup.spending hG ha ht i).1.old), ?_ ⟩
  ·
    intro N m n h
    change Bid.Sworn (M.H N m) n G
    by_cases ht : m=N
    · subst m
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hh',-⟩:= hT.layer
      rw [hh'.peak]
      exact WilsonStartup.Design.top_sworn _ (Canonical.direct_le_one (hT.paths.cap N N le_rfl).metric)
    exact he.waves _ _ _ (by omega)
  obtain ⟨U,V,X,-,-,-,-,hw,-,-,-,-,-,hy,hf⟩:=hT.layer
  let f:= fun (N i:ℕ)=> if i=N then 0 else u (a.clock.J i)
  change ∃ l,RankCovariance.ShapePort a M l
  refine ⟨f,⟨fun N m hm => ?_,fun N i hi=> ⟨(hy.guesses N i hi).trans (hw.2 _ _ hi).1, (hf N i hi).trans (hw.2 _ _ hi).2⟩⟩⟩
  obtain hh|rfl := lt_or_eq_of_le hm
  · rw [hy.other _ _ hh]; exact (show f N m=u (a.clock.J m) from if_neg hh.ne).symm ▸ hw.1 _ _ hh.le
  rw [show f m m=0 from if_pos rfl,Next.Free.loc_top,hy.peak]
  exact Planned.Port.Edge.express _ a.clock.kernel.penalty_pos _ (a.clock.adm m) _
end YM.PhysicalNext.Repeat
