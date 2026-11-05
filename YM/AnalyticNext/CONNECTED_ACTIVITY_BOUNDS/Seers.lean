import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Pens


/-!
# Expanded post-x pricing

Amounts uniform for qualifying S and T. No need a derivative appointment for phase knobs of
a Gauge. Real output prices multiply PC before forest structures; ticket κ never shrunk once S area identified.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Plotter
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths Chains Calls Mixed Cab Presented Canvas Coverage
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S}

def tender' (G : Gauge) (D : Patch) (x : ℝ) (ρ : Tempo) := (20 *constant)*amend G D x ρ.rate

def markBook (S : StepData c f) (R : Rep G f) (x κ a ε δ : ℝ) (ρ : Tempo) := Buy.quote G S.patch.L κ (1/4)
    a ε δ (retime R pit).beta x 2 0 (10*tab G S.patch x^7) (tender' G S.patch x ρ)

-- for true within-Step R. NarrowBand carried by same band premise `Lives`
def NarrowBand (G : Gauge) (L : Side) (x β : ℝ) := betaF G x L/2≤β ∧ β≤2*betaF G x L
lemma regional (G : Gauge) (D : Patch) {x β t : ℝ} (he : NarrowBand G D.L x β) (ht : |t|≤1/4)
    (hβ : 0<betaF G x D.L) : OnBand G D x (β*hour t) := by
  obtain ⟨hp,hl⟩ := he; have hv : 0≤β := by linarith
  obtain ⟨h1,h2⟩ := abs_le.mp ht
  have hg : 1/2≤hour t ∧ hour t≤2 := ⟨by unfold hour; nlinarith, by unfold hour; nlinarith⟩
  exact ⟨by linarith only [mul_le_mul_of_nonneg_left hg.1 hv,hp],by linarith only [mul_le_mul_of_nonneg_left hg.2 hv, hl]⟩





structure Rail (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (R : Rep G f) (x W r κ a ε δ : ℝ)
    (N : ChartRatio G) (t : Turns) (ρ : Tempo) : Prop where
  high : 0<R.beta
  gave : (markBook S R x κ a ε δ ρ).Buy S.patch.L 500 (radiusB x)
  took : ∀ (A : Stores S) (V : Config G c) (F : Forest S.ratio),cert S x A V → t.Takes
    (eyes S G (radiusB x)) (gram T F x A V) (dcol S) (paceR x)
  pack : ∀ (F : Forest S.ratio) (A p : Stores S) (Y : Mint T F A x), cert S x A Y.V →
    Y.u=holdSize G S.patch x → Y.r=r → Installed p A (450*radiusB x) → ∀ L z,
    4^(pulp F G p x)*(|pulse T x W R N L Y z (.inl p) pit|+|pulse T x W R N L Y z (.inl p) ridge|) ≤
      PackCost S (markBook S R x κ a ε δ ρ) p
  far : let b:= markBook S R x κ a ε δ ρ; let w:=constant*amend G S.patch x ρ.rate
    ∃ Z Z', Wake T R x W r N t pit Z b.head w ∧ Wake T R x W r N t ridge Z' b.head w ∧
      Mixed.Accounts S 500 (radiusB x) b (pOther T x R) (grant (takePaid t) Z Z') 0 (PackCost S b)


end YM.AnalyticNext.ConnectedActivity.Plotter
