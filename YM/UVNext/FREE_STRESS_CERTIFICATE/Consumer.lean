import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.SCHEDULE.Pre
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.PRICE_COMPILER.Suppression
import YM.UVNext.FREE_STRESS_CERTIFICATE.Certificate


/-! Discharge both red inputs *at the canonical MaxwellData being built*.
No change to lit/hers or comparator. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Climb Table Work.A01 Next.UVStress Function Set Filter MeasureTheory Analysis Extraction Ward Org Cells Spec
open YM.Spin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {S : Table C.book} {W : DiffPlan S}

/-- Exact stress/spec quantifier at positive or negative convention. The
additional antecedent is a choice of the actual polynomial, not a rank or
conservation promise. Construction of T (including κ and δ), and physical
estimates and their couplings not licensed here. -/
theorem from_data (hG : G.Simple) (T : MaxwellData C) (τ : ℝ) (ha : τ≠0) (ht : T.T.J=torch C.book.grid τ) :
    FreeDiv T.T T.hT T.lit.hers := certificate hG T.T T.hT T.lit.pales _ τ ha ht



-- Stronger version using also filled (note this doesn't supply any short distance
-- conditions). All F refinements are the original ones; also retain the tilt
-- and Jewel samples on a single curve.

end YM.UVNext.FreeStress
