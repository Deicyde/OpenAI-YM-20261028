import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Next.FLUCTUATIONS.Sector
import YM.Next.SCHEDULE.Dues
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.SectorNext.VACUUM_NORMALIZATION.Composition
import YM.SectorNext.VACUUM_NORMALIZATION.Factors


set_option warningAsError false
/-!
# Two distinct ledgers

It is possible to keep the same absolute determinant units when accounting
for vacuum normalizers, with exact compensators. But the physical **value**
which updates v' is the interacting vacuum scalar (even determining it just
on flat output V, where the explicit output loop vanishes). . It's NOT just the flat
stationary determinant; we leave the *true* interacting remainder. Even if
using `Vacuum.office`, its flat accounting B₀ might be a CUT
Gram, not the stationary Hessian. Keep that difference too. And don't use a
bound on v' as if it bounded α or vice versa.

Show the multiplicative/readout conversions, legitimate logs and
compatibility with the exact scalar and normalized updates on this path.
Doesn't claim to prove an estimate that the interacting remainder is small
(e.g. in vacuum or at varying V), or even a measure-change in auxiliary
Gaussian sectors. `weight` below is a comparison functional in
precisely defined unmasked determinant convention, NOT the pushed
density itself or a claim of Laplace approximation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.QuantumRates.Accounts
open Function Filter Lattice Wilson RG RG.Supply Precision Exterior Tree  Bid
open Extra.Iteration 
open SectorNext.Vacuum Next.Fluctuations.Sector MeasureTheory
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)

/-- Comparison on the true **full** Hessian at flat, in the very `flatLine`
units of `Counter` (probability Haar, A.scale per free link, β exponent
uses real Color dimension/unscaled Hessian etc.). `penaltyZ` scale also
included. No old v, E, coverage or gas. -/
def reference (O : ChartRatio G) (t : S.Choices) (p : Clip) (W : PathData G) (β : ℝ) :=
    prefactor S G β * flatLine F O β (hessian F t p W 0 0)

/-- Actual scalar vs that reference (separate ledger). Our bounds for this remainder can
be extensive. -/
def excess (O : ChartRatio G) (t : S.Choices) (R : Rep G f) :=
    Real.log (S.push R.beta (stripped R) 1 / reference F O t R.clip R.path R.beta)





/-- Exact v update with this ledger. Shows sign/units and missing
term. `P` must be certified against actual push (no pricing
or locality or derivations of the last term implied from mere splitting).
Works prior to whole History.Selected. -/
theorem split (O : ChartRatio G) (hO : LocalRatio O) (t : S.Choices) (R : Rep G f) (P : Rep G c)
    {σ C Λ δ w : ℝ} (hp : P.Lawful σ C Λ δ w) (hv : P.eval = S.push R.beta R.eval)
    (hb : 0 < R.beta) (hD : 0 < (hessian F t R.clip R.path 0 0).det) :
    0 < S.push R.beta (stripped R) 1 ∧
    0 < reference F O t R.clip R.path R.beta ∧
      P.v = (S.patch.L.val:ℝ)^4 * R.v + (-wires c * Real.log (S.penaltyZ R.beta G) +
        nt F * Real.log (gaussLink O R.beta) - Real.log (hessian F t R.clip R.path 0 0).det/2 + excess F O t R) / sites c := by
  let V := reference F O t R.clip R.path R.beta
  have h := S.penaltyZ_pos (G:=G) R.beta
  have ht := link_factor_pos O hO R.beta hb
  have hq := prefactor_pos R.beta (S:=S) (G:=G)
  have hs : 0<V := mul_pos hq (mul_pos (pow_pos ht _) (inv_pos.mpr <| Real.sqrt_pos.mpr hD))
  have hh : 0<S.push R.beta (stripped R) 1 := by rw [reveal S R P hp hv]; exact Real.exp_pos _
  refine ⟨hh,hs,?_⟩
  rw [SectorNext.Vacuum.update S R P hp hv]
  unfold excess
  unfold V at hs
  have hi := pow_pos ht (nt F)
  have hj := inv_pos.mpr (Real.sqrt_pos.mpr hD)
  rw [Real.log_div hh.ne' hs.ne',reference,flatLine,Real.log_mul hq.ne' (mul_pos hi hj).ne',
    Real.log_mul hi.ne' hj.ne',Real.log_inv,Real.log_sqrt hD.le,prefactor,
    Real.log_pow,Real.log_pow,Real.log_inv]
  unfold wires; ring

open Pressure Next.Fluctuations.Sector  

end YM.Further.QuantumRates.Accounts
