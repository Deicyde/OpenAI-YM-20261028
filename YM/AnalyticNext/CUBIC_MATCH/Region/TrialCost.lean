import YM.AnalyticNext.CUBIC_MATCH.Region.Scale

set_option warningAsError false

/-!
# Trial pays link and difference before rotation

The stencil is *already* a cover row of H. Use same one. Literal `sift`
counts in the quotient, use real color basis. First difference read with
`knock` applies down to the centered-cut step signs in `advanceC`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bloch Bid Matrix Work.F08 Next.Free
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {ι μ : Type*} {θ B C : ℝ} {L : Side}
  {c f : μ → Side}



section liftTrial
variable (hs : ∀ i : μ,(f i).val=(c i).val*L.val)

def mainRoot (p : μ) := (between hs p).embed



variable {T : Cross L (TypeFace 1) (TypeFace 1)}










end liftTrial
end YM.CubicMatch
