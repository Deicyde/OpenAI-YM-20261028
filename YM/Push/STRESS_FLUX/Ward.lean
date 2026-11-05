import YM.Push.STRESS_FLUX.Discrete

/-! Finite shell identities for arbitrary exterior Wilson words, in ambient-volume lattice
cutoff convention. These include the literal residual `anomaly` inside the sum (especially
*on* the enclosed insertion); it is not assumed small, nor treated as negligible based on
`price_balance` which is only a jet identity on unweighted smooth tests. `boundaryWeight` uses
shifted V, not just centered difference of χ times V at the node (these can differ for the
angular test). One can take *sharp* χ=characteristic of a set here (cross-boundary links), or
smooth sampled cutoff with contact stencil margins. The proposed B70 continuum construction
via matched insertions uses a different mechanism. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Discrete
open Function Set Filter Gauge Lattice Wilson RG MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} {N p : ℕ} (C : Family G)

def flux (w : Coeff) (N p) (χ : Site (C.side N p) → ℝ) (V : Site (C.side N p) → E4) (F : Config G (C.side N p) → ℂ) :=
    -(C.S.a N ^ 4 • ∑ x, ∑ b, ∑ a, boundaryWeight (C.S.a N) χ V x a b •
      moment (C.beta N p) (fun U => physical C w N p x U a b * F U))

def remainder (w : Coeff) (N p) (Zδ : ℝ) (χ : Site (C.side N p) → ℝ) (V : Site (C.side N p) → E4) (F : Config G (C.side N p) → ℂ) :=
    C.S.a N^4 • ∑ x, ∑ b : Axis, (χ x * V x b) • moment (C.beta N p) (fun U => anomaly C w Zδ x b U * F U)

def charges (N p) (Zδ : ℝ) (χ : Site (C.side N p) → ℝ) (V : Site (C.side N p) → E4) (F E : Config G (C.side N p) → ℂ) :=
    C.S.a N^4 • ∑ x, ∑ b : Axis, (χ x * V x b * Zδ) • moment (C.beta N p) (fun U => variation C x b F U * E U)
















/-- Exterior support condition (stronger than mere distinctness!). Even if overlaps are
allowed within E, no site in its supporting sets encounters an active Ward center x. Do not
infer this just from `χ (z i)=0`. -/
def Exterior {ι : Type*} (χ : Site (C.side N p) → ℝ) (E : ι → C.book.Token) (z : ι → Site (C.side N p)) :=
    ∀ x, χ x≠0 → ∀ i, x ∉ (C.localSection (E i).1).footprint (z i)



structure WardEstimate (w : Coeff) (N p : ℕ) (χ : Site (C.side N p) → ℝ) (V : Site (C.side N p) → E4) (Zδ : ℝ) (F E : Config G (C.side N p) → ℂ) : Prop where
  identity_ : flux C w N p χ V (F*E) = charges C N p Zδ χ V F E + remainder C w N p Zδ χ V (F*E)
  error_bound : ‖flux C w N p χ V (F*E) - charges C N p Zδ χ V F E‖ ≤ C.S.a N^4 * ∑ x, ∑ b : Axis, |χ x * V x b| *
    ‖moment (C.beta N p) (fun U => anomaly C w Zδ x b U * (F*E) U)‖






end YM.StressFlux.Discrete
