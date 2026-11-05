import YM.PREC.Stacks

/-!
Formula regards exp-chart array, V fixed while differentiating, physical counting
basis. Real log det and jacobian on supported germs. Do not use the array price
cap or Hessian statement as a bound on mask-differentiated functions across flags.
This is **not** a proof of any beta reset. On-shell vs off-shell, normalization,
unweighted paths winding plus period, ghosts/divergences etc all real blockers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Precision
open Lattice Wilson RG Matrix Exterior Finset Tree Function Bloch Laurent
open MeasureTheory Set
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff ENNReal

variable {c f n : Side} {S : StepData c f} {G : Gauge} {k : Ratio c f} {a : Levels G}

abbrev Key (B : Forest k) (G : Gauge) := B.Free × G.ColorIndex

-- Exponential slice neighborhood guard, native volume in G.Color. No
-- measure invariance assumed for additive tangent Hessians off shell.
structure ChartRatio (G : Gauge) where
  J : G.Color → ℝ
  scale : ℝ
  radius : ℝ

structure LocalRatio (Ñ : ChartRatio G) : Prop where
  scale : 0 < Ñ.scale
  patch : 0 < Ñ.radius
  inject : Set.InjOn G.lieExp (Metric.ball 0 Ñ.radius)
  pos (x : G.Color) : x∈Metric.ball 0 Ñ.radius → 0 < Ñ.J x
  anchored : Ñ.J 0=1
  germ : ∀ x∈ Metric.ball (0:G.Color) Ñ.radius, ContDiffAt ℝ ω Ñ.J x
  borel : Measurable Ñ.J
  actual : Measure.map G.lieExp ((volume.restrict (Metric.ball 0 Ñ.radius)).withDensity (fun x : G.Color => ENNReal.ofReal (Ñ.scale*Ñ.J x))) =
    G.probHaar.restrict (G.lieExp '' (Metric.ball 0 Ñ.radius))
  isOpen : IsOpen (G.lieExp '' (Metric.ball 0 Ñ.radius))

def frame (B : Forest k) (i : Key B G) : AxisChart G B := Pi.single i.1 (EuclideanSpace.basisFun G.ColorIndex ℝ i.2)

def hessian (F : Forest S.ratio) (t : S.Choices) (p : Clip) (R : PathData G)
    (u : fieldDir G c 1) (x : AxisChart G F) : Matrix (Key F G) (Key F G) ℝ := of fun i j =>
    iteratedFDeriv ℝ 2 (tested F t p R u) x ![frame F i, frame F j]

def thermal (F : Forest S.ratio) (t : S.Choices) (p : Clip) (R : PathData G)
    (ρ : fieldDir G c 1 → AxisChart G F) (A : ChartRatio G) (u : fieldDir G c 1) : ℝ :=
    loop R (lifting F (represent u) (ρ u)) + (1/2) * Real.log (hessian F t p R u (ρ u)).det -
        Real.log (∏ i : F.Free, A.J (ρ u i))

def draft (α : ℝ) (R : PathData G) (p : Clip) (u : fieldDir G c 1) := α*secondTerm p R (represent u)+loop R (represent u)

/-- Real direction plane wave section. E quadratic claim on complex amplitudes
(paired ±p) should be shown, paying constants to obtain all polarized real
entries requested here. When specifying approximation over *any two waves*,
not just opposite -- need ALSO translation invariance or comparable estimate.
No weakening via † at complex p. Norm on weights complex modulus.
-/
def wave (p : Site c) (σ : TypeFace 1 → G.ColorIndex → ℂ) : fieldDir G c 1 := fun x =>
    WithLp.toLp 2 (fun i => (cell p x.1 * σ x.2 i).re)

structure FiniteBound (F : Forest S.ratio) (R T : PathData G) (p q : Clip) (α : ℝ) (A : ChartRatio G)
    (ρ : fieldDir G c 1 → AxisChart G F) (Θ γ Λ : ℝ) : Prop where
  branch (t : S.Choices) : ∀ᶠ x in nhds 0, 0 < (hessian F t p R x (ρ x)).det
  born t : ContDiffAt ℝ ω (thermal F t p R ρ A) 0
  classicalResult : ContDiffAt ℝ ω (draft (c:=c) α T q) 0
  wave_price t (i j : Site c) (σ τ : TypeFace 1 → G.ColorIndex → ℂ) :
      (∀ x y, ‖σ x y‖≤1) → (∀ x y, ‖τ x y‖≤1) →
      let W := ![wave i σ,wave j τ]
      |iteratedFDeriv ℝ 2 (thermal F t p R ρ A) 0 W - iteratedFDeriv ℝ 2 (draft α T q) 0 W| ≤
        (Fintype.card (Site c):ℝ)*Θ*Λ*Real.exp (-γ*c.val)

/-- Series history, not derived from StepData alone. -/
structure Kin (M : Horizon a) (T : ChartRatio G) where
  alpha (N m : ℕ) : ℝ
  path (N m : ℕ) : PathData G
  stationary (N m p : ℕ) (F : Forest (a.clock.op m p).ratio) : fieldDir G (a.S.side m p) 1 → AxisChart G F

/-- Post-L costs; since T and P produced separately with same stamps call
must bind once. -/
structure PostCost {p : Supply.Sheet G} (m : Supply.Rolls p) where
  η : ℕ → ℝ
  Γ : ℕ → ℝ
  c : ℕ → ℝ
  g : ℕ → ℝ
  price j : 0 < η j
  pos j : 0 < Γ j
  posC j : 0 < c j
  posG j : 0 < g j

namespace Kin
variable {C : Horizon a} {O : ChartRatio G}
structure Planned (M : Kin C O) {s : Supply.Sheet G} {ŵ : Supply.Rolls s} (Q : PostCost ŵ) : Prop where
  stage : s.profile = a.clock.stage
  lengths : ŵ.L=a.clock.factor
  links N m : m ≤ N → Attached (C.H N m) (M.path N m)
  cap N m : m ≤ N →
    let j:=a.params m
    (M.path N m).Bounds j.clip j.width j.paths (a.clock.loopCap m)
  peak N p : ∀ j, j ≤ 4 → SameJet j (fun x => mainTerm (a.params N).clip (M.path N N) (represent (x:fieldDir G (a.S.side N p) 1)))
      (fun x => Wilson.energy (represent x))
  initial N b : ( (M.path N N).loop b).coeff=0
  gap N m p : m < N → ∀ F : Forest (a.clock.op m p).ratio,
      PriceGap F (a.params (m+1)).clip (M.path N (m+1)) (Q.η (a.clock.J (m+1)))
  critical N m p : m < N → ∀ F : Forest (a.clock.op m p).ratio,
      Critical F (a.params (m+1)).clip (M.path N (m+1)) (M.stationary N m p F) ∧
        Guessed F (installed (a.clock.op m p).ratio (C.towers N m).A0) (M.stationary N m p F)
  classicalPart N m p : m < N → ∀ F : Forest (a.clock.op m p).ratio,
    ClassicalMatch F (a.params (m+1)).clip (a.params m).clip (M.path N (m+1)) (M.path N m) (M.stationary N m p F)
  kinetic N m : m < N → |M.alpha N m + G.slopeConstant*Real.log (a.S.block m).val| + 1 ≤ (a.params (m+1)).drift
  retains N m p : m < N →
    let j:= a.clock.J (m+1)
    ∀ F : Forest (a.clock.op m p).ratio,
      FiniteBound F (M.path N (m+1)) (M.path N m) (a.params (m+1)).clip (a.params m).clip (M.alpha N m) O
        (M.stationary N m p F) (Q.Γ j) (Q.c j) (a.clock.loopCap (m+1))
end Kin
end YM.Precision
