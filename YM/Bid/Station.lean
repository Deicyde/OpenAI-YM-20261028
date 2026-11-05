import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.Bid.Energy




/-!
# input F01–F05 Taylor gates

Red staircase should deliver Bed & path the actual FStep uses. Curvature
corrections fPack accordingly. Use these WPs even when implementing correction
recursively: Hess doesn't see cubic/quartic updates, direction stays the same.
These tests in native directions use Frobenius unless written in sum. No
complex contour for POLY f assumed. No pre-L.W Peel. Adapters per-period
admitted only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Filter Function Lattice RG Wilson Precision Tree Exterior Bloch Laurent Pressure
open YM.Pressure.Stores Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal InnerProductSpace

variable {G : Gauge} {n c f : Side} {S : StepData c f}

-- implicit port. E01 use on arbitrary `Roll` with pays.i at enough periods. `Loom`
-- forces ratio/projector and root estimates same as here.
abbrev Dir (G : Gauge) (n : Side) := fieldDir G n 1

def gaugeFiscal (H : Bed) (x y : Dir G n) :=
    ∑ i : G.ColorIndex, dotProduct (parts _ _ x i) (K (H.metric.acts n)*ᵥparts _ _ y i)

def stretch (H : Forest S.ratio) (z : Dir G c × AxisChart G H) : Dir G f := fun i =>
    let x := (i.1,axisEquiv.symm i.2)
    (linearCopy S.ratio (collect G z.1)) x + if h : x∈ H.trunks then 0 else z.2 ⟨x,h⟩

def bills (S : StepData c f) (a : Dir G f) : Dir G c := fun e => WithLp.toLp 2 (fun i : G.ColorIndex => (probe S *ᵥ parts _ _ a i) e)
def crop (H : Forest S.ratio) (a : Dir G c × AxisChart G H) := a.1-bills S (stretch (S:=S) H a)

/-- Counting Hess of classical, all branches (no likelihood). -/
def Comptroller (H : Forest S.ratio) (B : Bed) (p : Clip) (W : PathData G) := ∀ k : S.Choices,
    let f := Function.uncurry (tested H k p W)
    f 0=0 ∧ fderiv ℝ f 0=0 ∧ ∀ a b, iteratedFDeriv ℝ 2 f 0 ![a,b]=
      gaugeFiscal B (stretch H a) (stretch H b) + S.kernel.penalty * ∑ i : Body 1 c, inner ℝ (crop H a i) (crop H b i)

def Prismatic (H : Forest S.ratio) (p : Clip) (W : PathData G) := ∀ k : S.Choices, ContDiffAt ℝ ω (Function.uncurry (tested H k p W)) 0

def pulled (a : Dir G n) (s : Signed) : Dir G n := fun b =>
    let p := posDir (axisEquiv.symm b.2); let v := p.rotate s
    let i := v.used (affine s 0 b.1)
    if v.neg then -a (i.1,coord i.2) else a (i.1,coord i.2)

def Sworn (B : Bed) (n : Side) (G : Gauge) := ∀ (s : Signed) (a b : Dir G n),
    gaugeFiscal B (pulled a s) (pulled b s)=gaugeFiscal B a b

/-- Can extend via analytic complex polynomial jets if prove at each
            fixed metric. ContDiffAt ω (not ∞) as required. -/
structure Fires (W : PathData G) (p : Clip) : Prop where
  crown {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (x : X) (n : Side) (A : X → Config G n) :
    (A x=1) → (∀ i, ContDiffAt ℝ ω (fun y => G.mat (A y i)) x) →
      ContDiffAt ℝ ω (fun y => mainTerm p W (A y)) x

def Larger (S : StepData c f) := S.patch.Branches S.kernel G ∧ 100*macroR S.patch ≤ f.val ∧ 1<c.val

/-- PB sensitivity. Use E02 Cops estimate with V=1 and actual smooth
                    tangents. -/
def F01 : Prop := E02 → ∀ (G : Gauge) (L : Side) (j : ℕ) (K : KernelChoices) (a : ℝ), 0<a → ∃ η : ℝ,0<η ∧
    ∀ (c f : Side) (S : StepData c f), S.kernel=K → S.patch.L=L → S.patch.J=j → Larger (G:=G) S →
    ∀ (H : Forest S.ratio) (B : Bed) (p : Clip) (W : PathData G) (A : ℝ),
      Floor B p f a A → Prismatic H p W → Comptroller H B p W → PriceGap H p W η

def F02 : Prop := ∀ (G : Gauge) (c : Clip) (W : PathData G) (σ C Λ : ℝ), W.Bounds c σ C Λ → Fires W c

/-- cochains & exact unnormalized shape; metric H symmetry required.
                P outputs call on any chosen StepData. Includes stationary matrix
                directions still at angles. -/
def F03 : Prop := ∀ (G : Gauge) (c f : Side) (S : StepData c f), Larger (G:=G) S →
    ∀ (H : Forest S.ratio) (B : Bed) (p : Clip) (W : PathData G) (σ C Λ a A : ℝ),
      Floor B p f a A → W.Bounds p σ C Λ → Attached B W → Sworn B f G →
        Fires W p → Prismatic H p W ∧ Comptroller H B p W

def HeatG (H : Forest S.ratio) (p : Clip) (W : PathData G) (ρ : Dir G c→AxisChart G H) (B : Bed) := ∀ i : S.Choices,
    SameJet 2 (fun x => tested H i p W x (ρ x)) (fun x : Dir G c => (1/2:ℝ)*gaugeFiscal B x x)

def F04 : Prop := ∀ (G : Gauge) (c f : Side) (S : StepData c f), Larger (G:=G) S →
    ∀ (H : Forest S.ratio) (B C : Bed) (p : Clip) (W : PathData G) (T : Towers S.patch.L) (a : ℝ),
      0 < a → Towers.Diagonal S B C T → Prismatic H p W → Comptroller H B p W → PriceGap H p W a →
        (∃ (q : Clip) (v e : ℝ), Floor C q c v e) →
        ∃ ρ, Critical H p W ρ ∧ Guessed H (installed S.ratio T.A0) ρ ∧ HeatG H p W ρ C

-- Haar determinant germ independence not just quadratic. 

def F05 : Prop := ∀ (G : Gauge) (c f : Side) (S : StepData c f), Larger (G:=G) S →
    ∀ (H T : Forest S.ratio) (p : Clip) (W : PathData G) (σ C Λ a b : ℝ) (ρ u),
      W.Bounds p σ C Λ → Critical H p W ρ → Critical T p W u → 0<a → 0<b →
      PriceGap H p W a → PriceGap T p W b → ∀ P : ChartRatio G, LocalRatio P → ∀ k : S.Choices,
      (fun x => tested H k p W x (ρ x))=ᶠ[𝓝 0] (fun x=>tested T k p W x (u x)) ∧
      ∃ cd : ℝ, thermal H k p W ρ P=ᶠ[𝓝 0] (fun x => thermal T k p W u P x+cd)

-- PER-CALL before Programs.
structure Scene (G : Gauge) (L : Side) (j : ℕ) (K : KernelChoices) (a : ℝ) : Prop where
  χ : ∃ η : ℝ, 0<η ∧ ∀ (c f : Side) (S : StepData c f), S.kernel=K → S.patch.L=L → S.patch.J=j → Larger (G:=G) S →
      ∀ (H : Forest S.ratio) (B C : Bed) (p q : Clip) (W : PathData G) (σ c₀ Λ m v u : ℝ) (T : Towers S.patch.L),
        Towers.Diagonal S B C T → Floor B p f a m → W.Bounds p σ c₀ Λ → Attached B W → Sworn B f G →
          Floor C q c v u → PriceGap H p W η ∧ ∃ ρ,Critical H p W ρ ∧ Guessed H (installed S.ratio T.A0) ρ ∧ HeatG H p W ρ C

lemma cospons (Y : E02) (A : F01) (B : F02) (C : F03) (V : F04) (L : Side) (j : ℕ) (K : KernelChoices) (a : ℝ) (ha : 0<a) : Scene G L j K a := by
  obtain ⟨b,hb,H⟩ := A Y G L j K a ha
  refine ⟨b,hb,fun c f S he ht hz hh F D I p q W σ y Λ m v u T HA HH Hp Hw HU hv => ?_⟩
  obtain ⟨ht',ht''⟩ := C G _ _ _ hh F D p W _ _ _ _ _ HH Hp Hw HU (B G p W _ _ _ Hp)
  have hk := H _ _ S he ht hz hh F _ _ _ _ HH ht' ht''
  exact ⟨hk,V G _ _ S hh F D I p W T b hb HA ht' ht'' hk ⟨_,_,_,hv⟩⟩
end YM.Bid
