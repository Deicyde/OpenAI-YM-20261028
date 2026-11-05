import YM.Planned.STATIONARY_JET_PORT.Measured

set_option warningAsError false

/-! Thermal analytic port including the *entering* loop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push Push.Uniform Filter Function Set Metric Lattice Matrix RG Precision Tree Bid
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {B : Forest S.ratio}
    {p : Clip} {R : PathData G} {Q : KernelChoices} {μ C Λ : ℝ} {N j : ℕ}
    {A : Before G μ C j Q (N+3)} {O : ChartRatio G}
    {g : In G c → AxisChart G B}

-- include old curvature cost Λ (can even be zero, then owe ≤0 from the entering loop itself)
def heirRate (Y : ChartPrices) (N : ℕ) (L : Side) (μ : ℝ) :=
  weaker (N+1) (litSpan (N+1) (pathRate Y N) (entryWidth (N+4) L μ))
def heirToll (G : Gauge) (Y : ChartPrices) (N : ℕ) (L : Side) (μ Z : ℝ) :=
  let v := entryWidth (N+4) L μ
  let r := litSpan (N+1) (pathRate Y N) v
  1 + |atomCost G Z μ (N+4) 2| * machinist (N+1) Y.coords (pathCost Y (N+1)) v * countCost (r/2)

-- aggregate tariffs (use coarser positive sums at deployment)
def caloricRate (Y : ChartPrices) (N : ℕ) (L : Side) (μ : ℝ) :=
  min (taxRate Y N) (min (heirRate Y N L μ)
    (logRate Y.coords N (transit Y N) (Y.gap/2) (chargeBill Y N)))
def caloricToll (O : ChartRatio G) (fee : ℝ) (Y : ChartPrices) (N : ℕ) (L : Side) (μ Z : ℝ) :=
  heirToll G Y N L μ Z +
    logging Y.coords N (transit Y N) (Y.gap/2) (chargeBill Y N) + tax O fee Y N

section Real
variable (hg : A.Service B p R g) (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q)
local notation "Y" => (A.tables p S.patch)
local notation "dim" => S.Choices
local notation "Inx" => (Positions (Primary c G))
lemma hasInheritance (hp : R.Bounds p μ C Λ) : 0 ≤ Λ := le_trans
  (tsum_nonneg (fun _ => hp.two.1 _)) hp.two.2.2
include hg hp hK hj ht


end Real

-- weakening rates to a common tariff doesn't affect order. Don't strengthen thresholds without proof.


structure AnalyticInput (B : Forest S.ratio) (Y : ChartPrices) (N : ℕ) (p : Clip) (R : PathData G)
    (D : FiberFee O (N+1)) (μ Z Λ : ℝ) (g : In G c → AxisChart G B) : Prop where
  guard : 0 < warm O Y N
  charts {x} : x ∈ ball (0:Positions (Primary c G)) (warm O Y N) →
    x ∈ domain (G:=G) (c:=c) Y ∧ ∀ i, g (tint G _ x) i ∈ ball 0 (O.radius/2)
  counter (t : S.Choices) : Counter Y N t p R g
  balance (t : S.Choices) {x} : x ∈ ball (0:Positions (Primary c G)) (warm O Y N) →
    let F := thermal B t p R g O ∘ tint G _
    ContDiffAt ℝ ω F x ∧ 0<caloricRate Y N S.patch.L μ ∧ 0<caloricToll O D.cost Y N S.patch.L μ Z ∧
      Scatter (account B G ∘ Sum.inl) (caloricRate Y N S.patch.L μ) (N+1) F x
        ((1+Λ)*caloricToll O D.cost Y N S.patch.L μ Z)

section Real
variable (hg : A.Service B p R g) (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q)
local notation "Y" => (A.tables p S.patch)
local notation "Inx" => (Positions (Primary c G))
include hg hp hK hj ht


end Real
end YM.Planned.JetPort
