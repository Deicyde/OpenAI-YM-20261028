import YM.Next.FLUCTUATIONS.Defs
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.OnTrack
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian
import YM.Work.B18

/-!
# Integrable domination and Gaussian integral prices on PI coordinates

For the limit argument. All such charges may cost the ENTIRE dimension.
Counting measures here in the sense of counting-coordinate Gaussian/Haar
(real vectors, not probability counting on configurations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open Function Filter WilsonStartup.Change Set Metric Matrix Asymptotics
open MeasureTheory ProbabilityTheory  Next.SectorChange.Gaussian
open scoped Topology BigOperators ContDiff

section scalar
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : ℝ × E → ℝ) (x : ℝ)




variable [FiniteDimensional ℝ E]


variable {F} {x}

end scalar

section integral
variable {ι : Type} [Fintype ι]
variable (F : ℝ × Vec ι → ℝ) (x : ℝ)

section matrix
variable [DecidableEq ι]
def values : Matrix ι ι ℝ := Matrix.of fun i j => Bends F x (Pi.single i 1) (Pi.single j 1)



def stamp : ℝ := coat (values F x)⁻¹

end matrix


end integral
end YM.PhysicalNext.FlatResponse
