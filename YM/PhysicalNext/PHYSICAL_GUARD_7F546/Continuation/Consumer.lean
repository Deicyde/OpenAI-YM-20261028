import YM.Next.BOUNDARY.Decomposition
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Measure
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Hill

/-!
# Using the held physical comparison on polynomial arrays

Folios bought on top of WeightedAt, with original z gauge and v.
No assumptions about weights/envelopes on favorable cylinders:
earn Paying on all licensed reads. Reference law for any P values is
independent of tree/tag/k/frozen Y, full `Current.fConditional` matrix
there, with same `floor`, uses FULL coarse-gauge field. No reconstruction
of actual PartII connection under *different* HAT/patch assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Rows Tree Bid Gaussian
open Extra.Iteration Extra.Iteration.Scales YM.AnalyticBridge.LocalGaussianLaws Current Lift Remote Local Assembly
open MeasureTheory SectorTools.PhysicalGaussianSwitch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

open FreeResolvent (treeInverse insertion ix flatten tensor)
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {I : Type} [Fintype I] [DecidableEq I]
    {T : Tube G S} {V : Config G c}


/-- Read at the actual physical data in this gaussian factor, no
intervening frame changes. -/
def photo {x : ℝ} (g : ℝ) (V : Config G c) (a : Vec (In x A F (G:=G))) (Y : LinkArray G (Frozen A x F))
    (Z : Vec (In x A F (G:=G))) := physical A F V Y (tape (a+g • Z))



/-- At normalized physical reads `g⁻¹*k`. u can optionally remove a
further deterministic centering, e.g. the linearized mean. `b0` tested
in the chosen frame. -/
structure Assessment (P : I → Occasion G f) (r : I → G.El) (X : Support f)
    (t x : ℝ) (g : ℝ) (L : Vec (In x A F (G:=G)) → Config G f)
    (Q : Gaussian.Table (In x A F (G:=G))) (B : Gaussian.Table I) (Γ : Vec (In x A F (G:=G)) → ℝ)
    (u b0 : Vec I) (Δ : Vec I → E) (C : ℝ) : Prop where
  reference : Integrable (fun z => Δ (b0-u+z)) (cloud B)
  forecastBound : ‖b0‖ ≤ t/g
  full : Integrable (fun z => Δ (sampled P r g (L z)-u)) (cloud Q)
  auth : Integrable (fun z => masked t X (fun V => Δ (sampled P r g V-u)) (L z)) (cloud Q)
  both : Integrable (fun z => Γ z • masked t X (fun V => Δ (sampled P r g V-u)) (L z)) (cloud Q)
  whole (z) : Γ z • Δ (sampled P r g (L z)-u) = Γ z • masked t X (fun V => Δ (sampled P r g V-u)) (L z)
  charged :
    ‖(∫ z, Γ z • masked t X (fun V => Δ (sampled P r g V-u)) (L z) ∂cloud Q)-
      ∫ z, Δ (b0-u+z) ∂cloud B‖ ≤ C*(3*x^(-(1/16):ℝ))
  bare :
    ‖(∫ z, masked t X (fun V => Δ (sampled P r g V-u)) (L z) ∂cloud Q)-
      ∫ z, Δ (b0-u+z) ∂cloud B‖ ≤ C*(4*x^(-(1/16):ℝ))
  unmasked : ‖(∫ z, Δ (sampled P r g (L z)-u) ∂cloud Q)-
      ∫ z, Δ (b0-u+z) ∂cloud B‖ ≤ C*(4*x^(-(1/16):ℝ))

section paying
variable {x β g U ε : ℝ} {H L : Bed} {o : Site c} {W : Finset (Bond f)} {X : Support f}
    {Y : LinkArray G (Frozen A x F)} {a : Vec (In x A F (G:=G))} {Q : Gaussian.Table (In x A F (G:=G))}
    {Pt : Patch} {l D : ℕ} {v : Dir G c}


end paying

/-- Add the post-P.L costs. Spacing already paid before. Conditions for
reads will all hold in *this* chosen gauge frame. Produce Payments for all
polynomial anchors, keep Mind choices/oracle hypotheses on the supplier. -/
def Folio (l D : ℕ) (x R E ε : ℝ) (T : Tube G S) (A : Stores S) (o : Site c) (H L : Bed) (V : Config G c)
    (z : Site c → G.El) (v : Dir G c) :=
    WeightedAt x R E A T H o V z v ∧
    0<x ∧ 0 < fiery G x S.patch.L ∧ ∀ F : Forest S.ratio,
    (∀ β : ℝ,x/2 ≤ β → β ≤ 3*x →
    ∀ (k : S.Choices) (q : Push.SectorMeasure.Chi) (d : ℝ) (s : Assembly.Geometry) (Y : LinkArray G (Frozen A x F)),
      let V:=Lattice.gauge z V; let Q:=palette T A F k x V s; let a:=portrait T A F k x V s q d Y
      ∀ X W, Covers X W → Reachable S o x W → Paying x β S.patch (o:=o) T H L V v Q a Y ε X W l D E) ∧
    -- exact on the full retained free law, even using rotated slots
    (∀ (I : Type) [Fintype I] [DecidableEq I] (P : I → Occasion G f) (r : I → G.El),
      let B := analyzer P r * plane S F
      let J := treeInverse G S F H.metric 0
      covView B J = sky P r H L T ∧ (sky P r H L T).PosSemidef ∧ MeasurePreserving (view B) (cloud J) (cloud (sky P r H L T)))





section spending
variable {x R U ε β : ℝ} {H L : Bed} {o : Site c} {l D : ℕ} {z w}
  (h : Folio l D x R U ε T A o H L V z w)
include h




end spending
end YM.PhysicalNext.PhysicalGuard7f546.Curved
