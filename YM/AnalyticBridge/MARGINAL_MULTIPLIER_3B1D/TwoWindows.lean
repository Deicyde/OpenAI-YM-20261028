import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Qualify

/-!
Qualification across two *actual* leaves (may change F, k, A, Y, z,
mean/covariance and readout or affine-row windows under the given `Binds`).
Both tested with ONE ordering/direction system. Same coarse base and scale,
foreground readings can be kept under charts before changing variables. Prices
NOT for unchecked modifications outside of true flag/binding domains.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Precision Tree Matrix Next.SectorChange.Schur Next.SectorChange.ResidualPrice
  FiniteMatrix Gaussian  Next.Foundations Push.Local  Leaf Kernel
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} {k : ℕ}
section letters
variable {V U : Config G f} {F F' : Config G f → ℝ} {s : Support f} {o : Site f} {P : BudgetPoint}

def Nearby {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) (D : Directions G f → Prop) (V V' : Config G f) (F F' : Config G f → E) (b : ℝ) := ∀ i : List (Directions G f), i.length ≤ k → (∀ v∈i,D v) → ‖leftDerivs F i V-leftDerivs F' i V'‖ ≤ b




def Route (k : ℕ) (P : BudgetPoint) (s : Support f) (o : Site f) (V U : Config G f) (a b : ℝ) :=
  k < P.order ∧ ∃ z : Directions G f, ∃ t : ℝ, P.dirBound o z ∧ a*|t| ≤ b ∧ Agrees s (increment V (t • z)) U ∧ ∀ r ∈ uIcc 0 t, Healthy P.threshold s (increment V (r • z))


/-- Alternatives available *at each* finite fine E comparison. For top jets
can't treat continuity as Lipschitz. The crude alternatives keep the actual
mask prices (no gain if crossing a contributing boundary unless E paid the
weight already). -/
def AlignedE (k : ℕ) (P : BudgetPoint) (s : Support f) (o : Site f) (V U : Config G f) (F : Config G f → ℝ) (a b : ℝ) := 0≤b ∧
  ((¬Healthy P.threshold s V ∧ ¬Healthy P.threshold s U) ∨ 2*a ≤ b ∨ Agrees (inspected s) V U ∨
    Route k P s o V U a b ∧ Healthy P.threshold s U ∨
    (Healthy P.threshold s V ∧ Healthy P.threshold s U ∧ Nearby k (P.dirBound o) V U F F b))
-- if route ends at U only on s, still check health U at those flags!

end letters

namespace Kernel
variable {S : StepData c f} {T : Tube G S} {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ]
  {P : Location f I J} {h h' : Kernel G c I J ρ} {R : Rep G f} {V : Config G c} {l : ℕ} {D : Directions G c → Prop} {a b r a' b' : ℝ}
structure MotionCost (l : ℕ) (D : Directions G c → Prop) (V : Config G c) (t : ℝ) (h h' : Kernel G c I J ρ) (a b : ℝ) : Prop where
  base : 0≤a
  slide : 0≤b
  cov i j : Nearby l D V V ((h.cov · i j)) ((h'.cov · i j)) a
  gram i j : Nearby l D V V (h.gram · i j) (h'.gram · i j) a
  flat i j : |h.flat i j-h'.flat i j| ≤ a
  signal i : Nearby l D V V (h.signal · i) (h'.signal · i) a
  offset i : Nearby l D V V (h.offset · i) (h'.offset · i) a
  draw i : Nearby l D V V (h.draw · i) (h'.draw · i) a
  mean i : Nearby l D V V ((t⁻¹:ℝ) • (h.mean · i)) ((t⁻¹:ℝ) • (h'.mean · i)) b


structure CompatibleActivities (R : Rep G f) (k : ℕ) (s o : Finset ℕ) (U W : Config G f) (m ℓ n δ : ℕ → ℝ) (rate : ℝ) : Prop where
  light i (hi : i∈s) : let r := R.activities.reg i; AlignedE k R.p r.support r.site U W (R.activities.E i) (m i) (rate*n i)
  heavy i (hi : i∈o) : 0 ≤ rate*δ i ∧ (Agrees (inspected (R.activities.forced i).support) U W ∨ 2*(ℓ i)≤rate*δ i ∨ ‖R.activities.K i U - R.activities.K i W‖ ≤ rate*δ i)

variable {F F' : Forest S.ratio} {A A' : Stores S} {x : ℝ} {k k' : S.Choices}
    {L : Leaf G A x F I J ρ} {L' : Leaf G A' x F' I J ρ} {Y z Y' z'} {q : Chi} {d δ w rate : ℝ} {s o B B' : Finset ℕ} {m n ℓ ε : ℕ → ℝ}


variable {Z : ChartRatio G} {y : Site c} {p : BudgetPoint} {E η K u v M C C' κ ν E₀ ξ α : ℝ}

end Kernel
end YM.AnalyticBridge.MarginalMultiplier3b1d
