import YM.Push.STRESS_FLUX.Discrete
import YM.Push.STRESS_FLUX.Jacobian
import YM.Push.STRESS_FLUX.Matching


/-!
Push the Haar-Jacobian piece to a one-sided shell (coordinate faces carrying
a real marker controlled by *quadratic* chord defects). Angular factor in
this correction also uses the shifted argument. Never integrate it by parts
through spectator positions; they stay fixed. Neither this correction nor
the remaining price anomaly has a vanishing-UV assumption here. Lattice
volume conventions identical to Discrete.Ward. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Rebate
open Jacobian Discrete Lattice Wilson MeasureTheory Function Filter Set Gauge
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {G : Gauge} {C : Family G} {N p : ℕ} {n : Side}

def weight (C : Family G) (x : Site (C.side N p)) (U : Config G _) (b : Axis) := (↑(C.beta N p) : ℂ) * ∑ i, (↑(⟪clover U x b i,siteForce U x i⟫_ℝ) : ℂ)
def residual (C : Family G) (w : Coeff) (t : ℝ) (x : Site (C.side N p)) (b : Axis) (U : Config G _) := Discrete.divergence C w x b U - t • ((C.S.a N^5)⁻¹ • Rebate.weight C x U b)


def sample (C : Family G) (F : Config G (C.side N p) → ℂ) (x b) := moment (C.beta N p) (fun U : Config G _ => (marker U x b:ℂ)*F U)


variable (χ : Site n → ℝ) (V : Site n → E4)
lemma advance (M : Site n → ℂ) (a : Axis) : (∑ x : Site n, (χ x * V x a) • (M x - M (x-step a))) =
    -(∑ x, (χ (x+step a)* V (x+step a) a - χ x* V x a) • M x) := by
  have he := Equiv.sum_comp (Equiv.addRight (step a : Site n)) (fun x => (χ x*V x a) • M (x-step a))
  simpa only [smul_sub,sub_smul,Finset.sum_sub_distrib,neg_sub,sub_right_inj] using (by simpa only [show ∀ x : Site n, Equiv.addRight (step a : Site n) x = x + step a from fun _ => rfl,add_sub_cancel_right] using he.symm)

variable (C) in
def crossing (t : ℝ) (χ : Site (C.side N p) → ℝ) (V : Site (C.side N p) → E4) (F : Config G (C.side N p) → ℂ) :=
    ∑ x, ∑ b : Axis, (t / C.S.a N * (χ (x+step b)* V (x+step b) b - χ x* V x b)) • sample C F x b
variable (C) in
def unrebated (w : Coeff) (t : ℝ) (χ : Site (C.side N p) → ℝ) (V : Site (C.side N p) → E4) (F : Config G (C.side N p) → ℂ) :=
    (C.S.a N)^4 • ∑ x, ∑ b : Axis, (χ x* V x b) • moment (C.beta N p) (fun U => residual C w t x b U * F U)

section Ward
variable (C : Family G) (w : Coeff) (t : ℝ) (χ : Site (C.side N p) → ℝ) (V : Site (C.side N p) → E4)



end Ward


end YM.StressFlux.Rebate
