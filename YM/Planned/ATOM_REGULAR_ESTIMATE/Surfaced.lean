import YM.Planned.ATOM_REGULAR_ESTIMATE.Echo
/-!
Single-sample `Shoots` for any census making a transport from actual stationary
surface. Useful only for a principal kernel construction paying the other costs as
well. `hint` below represents log fluctuations (any gauge conversion already
applied); IN ADDITION needs information on the **linear** part of stationary
S (`LinearVals`) which Uniform's tables don't buy. Doesn't roll an unmatched
period stencil into another patch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Foliage
open Function Set Metric Filter RG Wilson Precision Lattice Tree Pressure Bid Push Uniform Next.Foundations
open WardBin.Lies Short Sample Collar
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

section Charges
variable {G : Gauge} {n m L : Side} {k d l : ℕ} {P : BudgetPoint} {X : Support n} {o : Site n} {c a b : ℝ}
variable {u v : Directions G n}

/-- Just restrict to retained reads. -/
def pane (P : BudgetPoint) (o : Site n) (X : Support n) : Directions G n →L[ℝ] Directions G n :=
    ContinuousLinearMap.pi fun e => if e∈screens X then (ContinuousLinearMap.proj e).comp (suppress P o) else 0







end Charges

section Billed
variable {G : Gauge} {n m : Side} {k K i j l d : ℕ} {S : StepData m n} {B : BudgetPoint} {F : Forest S.ratio}
    {u t W a c c' C η δ w r : ℝ} {Q : KernelChoices} {A : Before G u t j Q K} {P : Clip} {J : Collar G k}
    {R : PathData G} {φ : Phi G m n} {g : In G m → AxisChart G F} {X : Support n} {o : Site n}
    {T : Sample G m n} {z : T.Z} {V : Config G m} {D : Slab G m l}



def first (B : BudgetPoint) (X : Support n) (o : Site n) (φ : Phi G m n) (g : In G m → AxisChart G F) :=
    (pane B o X).comp (ray (plain φ g))




/-- External *linear* estimate. Keep on this stencil at actual orders. Tests
higher derivatives of the PANEL path (not requiring they be nonzero). -/
structure LinearVals (B : BudgetPoint) (X : Support n) (o : Site n) (φ : Phi G m n)
    (g : In G m → AxisChart G F) (d : ℕ) (c : ℝ) (x : Panels l → Origin G m) : Prop where
  starts : Taper B o X (screens X) d S.patch.L c (first B X o φ g (x 0))
  alters i (h : 0 < i) : i ≤ l → ∀ v : Fin i → Panels l, (∀ j, ‖v j‖ ≤ 1) →
    Taper B o X (screens X) d S.patch.L c (first B X o φ g (iteratedFDeriv ℝ i x 0 v))


end Billed
end YM.Planned.AtomRegular.Foliage
