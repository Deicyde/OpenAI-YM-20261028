import YM.Bid.Station
import YM.Push.STRESS_FLUX.Clover
import YM.Push.STRESS_FLUX.Cylinder
import YM.Push.STRESS_FLUX.Haar


/-! Normalized finite Ward identities with explicit breaking and contact terms. Symmetric
choice of link probes via clovers; use *both* directed variations (Haar divergence/force
and contacts). No assumption of a weight at which the residual can be thrown out. The tensor
being tested is on the ACTUAL normalized field calibration, not a differing discretization
on a more symmetric regulator. E takes another route past these issues in the continuum:
see the product matching construction separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Discrete
open Function Set Filter Gauge Lattice Wilson RG MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {N p : ℕ} (C : Family G)

abbrev device (x : Site n) (b i : Axis) (U : Config G n) := clover U x b i

def contraction {V : Type*} [AddCommGroup V] [Module ℝ V] (a : ℝ) (f : Step → V) := (a^5 * 2)⁻¹ •
    ∑ i : Axis, (f (posDir i) - f (negDir i))

def variation (x : Site (C.side N p)) (b : Axis) (F : Config G (C.side N p) → ℂ) (U) :=
    contraction (C.S.a N) (fun d => contact x d (device x b d.dir) F U)

def balance (x : Site (C.side N p)) (b : Axis) (U : Config G _ ) :=
    contraction (C.S.a N) (fun d => (↑(equation (C.beta N p) x d (device x b d.dir) U) : ℂ))








/-- Normalized lattice divergence of the *calibrated* stress candidate T. -/
def divergence (w : Coeff) (x : Site (C.side N p)) (b U) := (2 * C.S.a N)⁻¹ • ∑ a : Axis,
  (physical C w N p (x+step a) U a b - physical C w N p (x-step a) U a b)

def anomaly (w : Coeff) (Zδ : ℝ) (x : Site (C.side N p)) (b U) := divergence C w x b U - Zδ • balance C x b U













section SBP
variable {t : ℝ} {χ : Site n → ℝ} {V : Site n → E4}



def boundaryWeight (t : ℝ) (χ : Site n → ℝ) (V : Site n → E4) (x : Site n) (a b : Axis) := (2*t)⁻¹ *
    ((χ (x+step a)-χ x)* V (x+step a) b + (χ x-χ (x-step a))* V (x-step a) b)




end SBP
