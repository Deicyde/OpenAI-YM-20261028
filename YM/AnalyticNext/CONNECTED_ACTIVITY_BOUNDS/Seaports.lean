import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Hour
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Hyssop
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Redcap
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Wax

/-!
# Issuing the numerical calls on the actual step

Strengthening of `AbsoluteSums.Buy.sectors` and `SectorMeasure.full_grant` buys both
on the SAME κ. Here use POINT charge, the input these use inside, and their actual receipts, not
pretend their existential tokens can be fired individually. `sabres` records the literal Buy.sectors
result on the given κ (usable besides the strengthened one, any further such post tests via same witness).
Pre-L may depend on output exponent choice, but once known, any L bigger, in this ONE price call. `W`
set pre-Beta. Still must deploy on a regime with F, Ringing, etc and pay cuts. Does not issue Horizon,
Alongside, full histories. Uses valid `R` prices on step exactly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Due
open Function Lattice RG Precision Wilson Pressure Pressure.Stores MeasureTheory Push.SectorMeasure
open Matrix Push.SectorMeasure.Oriented Push.AbsoluteSums Tree Next.Fluctuations Filter Win Win.Promise Finset
open Centered Aff Aff.Mint Wages Jewels Presented  Mixed Work.E03 Exterior Bloch Turn Calls Coverage Packets
open YM.Progress.StationaryScenes YM.Input Pressure.Testing RG.Supply RG.Shoot Cab
open scoped Topology BigOperators ENNReal InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

-- synth stamp body, to test comparison across the two upstream existential statements

def bay (P : Teller G) (L : Side) (W μ : ℝ) :=
    ∀ u a ε δ D z : ℝ, ∀ d l : ℕ, 0 < u → 0 < δ → 0 ≤ a → 0 < ε → 0 ≤ D → z < 2 →
    ∀ᶠ x : ℝ in atTop, ∀ (β C extra spend γ : ℝ),
      let B := radiusB x; let fee := D*Delay.bill G L x^d*Delay.fineMonitor G L x^z
      (u*betaF G x L ≤ β) → 0 ≤ extra → 0 ≤ C → C ≤ Real.exp fee → spend+2*ε*extra ≤ fee →
      0 ≤ γ → γ ≤ Buy.tolerance δ B →
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L →
        100*(1+radiusB x) ≤ c.val → P.Funds S T →
      ∀ (F : Tree.Forest S.ratio) (U : Config G f) (V : Config G c) (j : S.Choices), Stores.SliceSet S F U →
        let b := Buy.quote G L μ u a ε δ β x C extra spend γ
        ∀ (ι : Type) (X : ι → Support c) (w e : ι → ℝ), (∀ i,0 ≤ e i) → (∀ i,0 ≤ w i) →
          Ac.Hit X B (Reserves.tariff w e (fun _ => 0) ε) b.head γ →
        ∀ g : Stores S → S.Choices → ℝ,
          (∀ A, Packets.connected S l B A → Stores.Plot A U j V x W →
            |g A j| ≤ C * Real.exp (spend*A.shares)) →
          let p := fun A => Grant.paid T x W β U V g A j
          b.Buy S.patch.L l B ∧ ∀ (m k r : ℕ) (v : ℝ),
          Ac.Hit (fun s => s.biUnion (foot S l B X)) B
            (Mixed.selected S l B b X w e p m k r v) b.exponent (b.ceiling m k r v)



-- post-step purposes independently require Govt prosecution etc. P,F.T stage quota.

def demandHead (a δ ε l : ℝ) := a+2*l+δ+2*ε+δ

-- Pre gauge request. Include client with P.top supportExponent (canonical Lives part) for any matching.
structure Park (P : Teller G) (L : Side) (a C δ ε η l : ℝ) : Prop where
  wrench : Jewels.wedge P C L
  H : ∀ D : Patch, D.L=L → ∀ᶠ x : ℝ in atTop,
      ∀ (A : Levels G) (m p N : ℕ) (T : Tube G (A.clock.op m p)) (B : Recipe A) (Y : Rep G (A.S.side (m+1) p)),
        (A.clock.op m p).patch=D → A.clock.hatBeta m=x → A.params (m+1)=P.top → T.high=(A.params (m+1)).clip →
        T.up=B.path N (m+1) → Lives B N (m+1) p Y → Y.beta ∈ band A (m+1) → Client P T Y η (demandHead a δ ε l) x



-- True analytic booking flags. Patches have L post-floor
structure Library (P : Teller G) (N : ChartRatio G) (r : ℝ) (D : Patch) (x C W κ a δ ε η l : ℝ) (ρ : Tempo) : Prop where
  high : 0<x ∧ 0<fiery G x D.L ∧ 0<radiusB x
  boats : ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (_F : Tree.Forest S.ratio), S.patch=D →
    P.Funds S T →100*(1+radiusB x)≤c.val → PointCharge T x W κ → Charged T x W κ ∧ Optic T x C ∧ Guest S T x W C r ∧
    ∀ (A A' : Bed), Alongside A A' T → ∀ R : Rep G f, let b := chosen S x R.beta G (a+2*l+δ) δ ε κ ρ.up.up
    Client P T R η (demandHead a δ ε l) x → FeeBook T x W r R N b ∧
    ∃ y : Zones T R x→ℝ,(∀ (F : Tree.Forest S.ratio) (B : Chi) (V : Config G c) (i : Zones T R x), ‖centre T x W r N R F B i.val V‖≤y i) ∧
      (∀ i,0≤y i) ∧ Trees.Ready (buses T R x) (radiusB x) (Reserves.tariff y (fun _=>0) (stamped T R x κ) l)
        (a+2*l) (budget_co G D x ρ) δ (budget_q G D x ρ)



-- uniform grants. Keep alongside separately needed by the integrator. Existence of T not here.

end YM.AnalyticNext.ConnectedActivity.Due
