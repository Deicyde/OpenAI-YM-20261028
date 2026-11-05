import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Arc.Totals
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Aperture
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Funds

/-!
# Sustaining charges of nonlinear faces and their curvature compare

Option to spend also on ONE guard, the usual polynomial comparison in E
(on suppressed-transport coordinates, to uncut), if it doesn't act until
leaving the ROM cube threshold. ζ includes SAME affine mean corrections.
Integrability paid even if not cutting here. No conclusion on volume or
work spread costs, long paths, partner terms. This is pricing the genuine
Gaussian components *before* declaration of gates or correction factors.
All absolute/moment certificates on same data and degree.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Arc
open AnalyticBridge.LocalGaussianLaws Venue Sweep SectorTools
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Local
open Primitives.GCC.LocalPolynomial (Script)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

section final
variable {α β I : Type} [MeasurableSpace α] [MeasurableSpace β] [Fintype I]

-- Argument names: f actual issued nonlinear, f₀ read on lamp's
-- linearization (source), f₁ read on uncut harmonic curvature (ideal).
structure Receipts (K D : ℕ) (E x B M : ℝ) (μ : Measure α) (ν : Measure β) (Y : α → Gaussian.Vec I)
    (f f₀ : α→ℂ) (f₁ : β→ℂ) : Prop where
  meas : Measurable f
  first : Integrable f μ
  cover : (∫ z, ‖f z‖ ∂μ) ≤ M * heat (Fintype.card I) K E (2*D)
  second : Integrable (fun z => ‖f z‖^2) μ
  wider : (∫ z, ‖f z‖^2 ∂μ) ≤ M^2 * heat (Fintype.card I) K E (4*D)
  aligned : Sweep.Savings K E (M * normalBill K E D) μ Y f₀
  changes : (∫ z, ‖f z-f₀ z‖ ∂μ) ≤ M*((D:ℝ)*B)*heat (Fintype.card I) K E (2*D+2)
  across : Integrable f₁ ν
  covers_far : (∫ z, ‖f₁ z‖ ∂ν) ≤ M * normalBill K E D * kiln K E
  second_far : Integrable (fun z => ‖f₁ z‖^2) ν
  wider_far : (∫ z, ‖f₁ z‖^2 ∂ν) ≤ (M * normalBill K E D)^2 * kiln K E
  horizon : ‖(∫ z,f₀ z ∂μ)-(∫ z,f₁ z ∂ν)‖ ≤ M * normalError K E D x

variable {K D : ℕ} {x E B M : ℝ} {μ : Measure α} {ν : Measure β} {Y : α → Gaussian.Vec I} {f f₀ : α→ℂ} {f₁ : β→ℂ}





-- Cube allowance. Apply e.g. with Stage2 tail certificate.



end final

section issue
variable {tier : ℕ} {G : Gauge} {c f : Side} {S : StepData c f} {x E R β : ℝ}
variable {V : Config G c} {W : Site c→G.El} {v : Dir G c} {T : Tube G S} {o : Site c}
variable {H B : Bed} {F : Forest S.ratio} {A : Stores S} {K D : ℕ}
variable {a l n m : ℝ} (hS : Larger (G:=G) S) (ha : 0<a) (hn : 0<n)
    (hH : Floor H T.high f a l) (hB : Floor B T.low c n m) (ht : Towers.Diagonal S H B T.R)
    (hc : Account tier K D E x A T H o V F W v) (hK : D+1 ≤ K)
    (k : S.Choices) (q : Chi) (d : ℝ) (s : Assembly.Geometry) (Y : LinkArray G (Frozen A x F))
    (hβ : 0 < β) (h : β ≤ 3*x) (he : Clears A x o (vista tier x))
variable {I : Type} [Fintype I] (u : I → Slot G f 2) (hu : interior tier S o x u)

-- Constants from pre-purchases; NEVER choose after seeing S etc.










include hS ha hn hH hB ht hc hK hβ h he hu



end issue
end YM.PhysicalNext.WeightedGaussianMarginal45C.Arc
