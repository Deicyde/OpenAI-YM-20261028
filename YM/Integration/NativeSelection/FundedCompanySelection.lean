import YM.FullVolume.Roll.Linger
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry

/-! Buy an additional prediction on the exact factor that the native company
constructs. The expense dictionary and programs exist before the joint length
floor. The register, protection and stage records then exist before the extra
delay and the original company's final delay are chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeSelection.FundedCompanySelection
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

/-- A predicate on the actual physical factor, including its dependent alloy. -/
abbrev Prediction (G : Gauge) :=
  {M : Metals G} → {D : Rolls M.p} → {A : Alloy M D} → Roost.Factor A → Prop

variable {G : Gauge}

/-- Prepay at one specified retargeted price. The sheet and chart are kept
through both stages of payment. -/
def Prepaid (F : Prediction G) (s : Sheet G) (price : MapPrices) : Prop :=
  ∀ (R : Targets s price) (E:Expenses R) (hc:∀ i j,(R i j).table=Next.Foundations.chart G) (C:Programs s) (z:Return.Wages) (bt:Baton G),
       (∀ i j, (E i j).wanting=-(7/16:ℝ)) → ∃ u :ℕ→ℕ, ∀ l : ℕ→ℕ,u≤l → ∀ (D:Rolls (ThroughLaunch.raise s l))
        (w:Return.Wages) (U:ℕ→ℝ) (Z:PhysicalNext.Repeat.Register D E w U) (φ:ℕ→ℕ→Postage) (S:Time.Scouts (F:=φ))
        (θ:Protection D) (p:ℕ→ℕ→JointLoad.Heir.Record) (P:PostCost D) (V:Delays θ),
         (∀ j i,Push.PriceCompiler.StepStages j i → s.first ≤ i → (p j i).ε≤1/4) →
        ∃ W:Delays θ,DelayLe V W ∧ ∀ W',DelayLe W W' → ∀ (K:Bar W')(I:Wait K)(hp:Stock.Priced W')
         (B0:Directed G I (chart G) (price) P),
           let A := (Alloy.mk P θ W' K I hp B0 : Alloy ((⟨ThroughLaunch.raise s l,price,chart G,chart_ok G⟩ : Metals G)) D)
           ∀ η q E' X J K' b,
             ∀ hZ : Roof.Sheltered (C:=C) (B:=K') A bt z (rays s) mile b X p J Z S (1/16) (1/16) (1/8) E' q η,
             ∀ hY : WorksIn (D:=D) (X:=(⟨ThroughLaunch.raise s l,price,chart G,chart_ok G⟩ : Metals G)) Z P W' S, ∀ hm:AsDivisors B0.a.S,
                F (⟨E',φ,S,η,q,w,K',R,E,U,Z,bt,z,rays s,mile,b,C,X,p,J,hZ,hc,hY,hm⟩: Roost.Factor A)

variable (hG : G.Simple) {s:Sheet G} {O K:MapPrices} {u g k:ℕ→ℝ} {r:Bid.Worth} {T': Further.StrongStartup.Tariffs} {Θ: Extra.Multi.Scope} {v:ℕ→ℕ} (h : ThroughLaunch.Perceived s O K u g k r T' Θ v)

include hG h
/-- The complete native purchase with its prediction on the same emitted
factor. The two numerical increases occur before their original choices. -/
theorem company {pred : Prediction G}
    (paid : Prepaid (@pred) s (ThroughLaunch.raging s K)) {τ : ℝ} (ht' : 0 < τ) : ∃ (j : ℕ→ℕ) (C : Programs s) (z : Return.Wages) (R:Targets s (ThroughLaunch.raging s K)) (E : Expenses R) (bt : Baton G), v ≤ j ∧
    (∀ i k,(R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=Roof.rays s i k ∧ (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0) ∧ ∀ l : ℕ → ℕ,j≤l → Nonempty (Rolls (ThroughLaunch.raise s l)) ∧ ∀ D : Rolls (ThroughLaunch.raise s l),
      ∃ y : Return.Wages, ∀ w : Return.Wages,y≤w → ∃ (u' : ℕ→ℝ) (R' : PhysicalNext.Repeat.Register D E w u') (B:ℕ→ℕ→Cafe), ∀ K' : ℕ→ℕ→Postage,
        ∃ (F : ℕ→ℕ→Postage) (S : Time.Scouts (F:=F)), (∀ i j, (F i j).rate ≤ (K' i j).rate) ∧ Pocket R' S ∧ ∀ (E₀ : ℕ→ℕ→Next.Scheduling.Exchange) (ξ : Extra.Multi.Tariff),
          ∃ (q : UVNext.CouplingReset.ResetPrices) (η : ℕ→ℝ) (P : PostCost D), ∀ θ₀ : ℕ → ℝ, (∀ j, 0 < θ₀ j) → ∃ θ : Protection D, θ.theta ≤ θ₀ ∧
           ∃ p : ℕ→ℕ→JointLoad.Heir.Record, (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) ∧
             ∀ (Q : ℕ → ℕ → JointLoad.Clockwork.Menu) (U : Delays θ), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→JointLoad.Folio.Aux,
               ∃ W : Delays θ, OrderedDelays W ∧ DelayLe U W ∧
               ∀ V, DelayLe W V → ∀ (Z : Bar V) (I : Wait Z) (a : Levels G) (_ : Paid I a),
                 Doors.Budget a k r ∧ Extra.Multi.Prepared Θ ξ (Next.Foundations.localSection G) a ∧ ∃ (hp : Stock.Priced V) (B' : Directed G I (chart G) (ThroughLaunch.raging s K) P),
                   let Y := (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.bountyV s K l) D)
                   B'.a = a ∧ Sheltered (C:=C) (B:=B) Y bt z (rays s) mile b Q p J R' S (1/16) (1/16) (1/8) E₀ q η ∧ Sheltered (C:=C) (B:=B) Y bt z (rays s) mile b Q p J R' S τ τ (1/8) E₀ q η ∧ Planned.Port.AtTop B'.kin ∧ Stationary.Artes.Cadre P B'.kin ∧ Next.Free.Amplify B'.M ∧ WorksIn (D:=D) (X:=ThroughLaunch.bountyV s K l) R' P V S ∧
                   Use.Origins B' ∧ (AsDivisors a.S → Use.Offering B' S w (radiusW B)) ∧
                   (∃ f, RankCovariance.ShapePort B'.a B'.M f) ∧
                   ∀ (hc : ∀ i j, (R i j).table = chart G)
                     (hZ : Sheltered (C:=C) (B:=B) Y bt z (rays s) mile b Q p J R' S (1/16) (1/16) (1/8) E₀ q η)
                     (hY : WorksIn (D:=D) (X:=ThroughLaunch.bountyV s K l) R' P V S)
                     (hm : AsDivisors B'.a.S),
                     pred (⟨E₀,F,S,η,q,w,B,R,E,u',R',bt,z,rays s,mile,b,C,Q,p,J,hZ,hc,hY,hm⟩ : Roost.Factor Y) := by
  obtain ⟨j, C, z, R, E, bt, hv, hE, purchase⟩ := companyK hG h ht'
  obtain ⟨u, fund⟩ := paid R E (fun i k => (hE i k).1) C z bt
    (fun i k => (hE i k).2.2.2.1)
  refine ⟨j ⊔ u, C, z, R, E, bt, hv.trans le_sup_left, hE, ?_⟩
  intro l hl
  obtain ⟨original, extra⟩ := sup_le_iff.mp hl
  obtain ⟨lengths, next⟩ := purchase l original
  refine ⟨lengths, ?_⟩
  intro D
  obtain ⟨y, wages⟩ := next D
  refine ⟨y, ?_⟩
  intro w hw
  obtain ⟨duration, reg, rider, register⟩ := wages w hw
  refine ⟨duration, reg, rider, ?_⟩
  intro initialPost
  obtain ⟨post, scouts, rates, pocket, postage⟩ := register initialPost
  refine ⟨post, scouts, rates, pocket, ?_⟩
  intro exchange tariff
  obtain ⟨q, η, P, protect⟩ := postage exchange tariff
  refine ⟨q, η, P, ?_⟩
  intro θ₀ hθ₀
  obtain ⟨θ, hθ, stages, quarter, delays⟩ := protect θ₀ hθ₀
  refine ⟨θ, hθ, stages, quarter, ?_⟩
  intro menu V
  obtain ⟨W, hVW, predicts⟩ :=
    fund l extra D w duration reg post scouts θ stages P V quarter
  obtain ⟨b, booth⟩ := delays menu W
  refine ⟨b, ?_⟩
  intro aux
  obtain ⟨W', ordered, hWW', output⟩ := booth aux
  refine ⟨W', ordered, hVW.trans hWW', ?_⟩
  intro V' hV' bar wait a ha
  obtain ⟨budget, prep, hp, B, hA, shelter, shelterτ, port, cadre,
      amplify, works, origins, offering, rank⟩ := output V' hV' bar wait a ha
  refine ⟨budget, prep, hp, B, hA, shelter, shelterτ, port, cadre, amplify,
    works, origins, offering, rank, ?_⟩
  intro _ hZ hY hm
  exact predicts V' (hWW'.trans hV') bar wait hp B η q exchange menu aux rider b hZ hY hm

end YM.Integration.NativeSelection.FundedCompanySelection
end
