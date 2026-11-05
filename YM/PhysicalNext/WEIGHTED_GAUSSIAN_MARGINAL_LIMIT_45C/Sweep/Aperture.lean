import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Venue.Space

/-!
# Observable through the physical d_1 Z, still centered Gaussian records

Prove exact closure onto the *same* admissible read set and numerical
path already present. Need every endpoint (including tree convention) and
same cuts. Select any list of stencil curvature reads u, interior by one
of the licensed patch. Prove also exact measures vs retained uncut
`fConditional`, which may be singular on such reads; there is no density
exchange on the curvature spaces (do the comparison from the active
coordinates instead). Not using any such identity for a re-cut formal
kernel which need not even be PSD.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
open AnalyticBridge.LocalGaussianLaws Venue
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Local
open SectorTools
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff ENNReal

variable {tier : ℕ} {G : Gauge} {c f : Side} {S : StepData c f} (A : Stores S) (F : Forest S.ratio)

section reduce
variable {I J L : Type} [Fintype I] [Fintype J]



omit [Fintype J] in
/-- Even if selects dependent rows! -/
lemma measured_curve [Fintype L] [DecidableEq L] [DecidableEq I] {C : Gaussian.Table I}
    (h : C.PosSemidef) (M : Matrix J I ℝ) (f : L→J) :
    MeasurePreserving (fun z : Gaussian.Vec I => (M*ᵥz) ∘ f) (cloud C)
      (cloud ((M*C*M.transpose).submatrix f f)) ∧
    ((M*C*M.transpose).submatrix f f).PosSemidef := by
  let B := M.submatrix f id
  have ht : (M*C*M.transpose).submatrix f f = PhysicalGaussianSwitch.covView B C := by
    unfold PhysicalGaussianSwitch.covView
    ext i j; simp [B, Matrix.submatrix_apply,mul_apply]
  rw [ht]
  exact ⟨PhysicalGaussianSwitch.view_cloud h B, PhysicalGaussianSwitch.covView_posSemi B h⟩
end reduce

section ports
variable (x : ℝ) (o : Site c) {I : Type}





def interior (tier : ℕ) (S : StepData c f) (o : Site c) (x : ℝ) (u : I → tileP (G:=G) (f:=f)) :=
    ∀ i, separation o (seat S 2 (u i))+1 ≤ vista tier x/4



end ports
end YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
