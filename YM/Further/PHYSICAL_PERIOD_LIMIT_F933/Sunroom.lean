import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.LocalLedger
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Rainy

/-! # Analytical compatibility of the full implicit jets

Give quantitative estimates in separate file; no blanket
assumption of uniqueness of continuation is needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Rainy
open Gauge Filter Jacobi Macrame Macrame.Lace Polytrace Withdrawal Liquid Enamel Loom Function Lattice RG Tree Matrix Finset Precision Exterior Bid Wilson Set Metric Push.Uniform Push Shingle Pitch Extra.Iteration Extra.Iteration.Calibration
open scoped Topology ContDiff BigOperators Classical

variable {d : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
variable {P Q : Positions (ι⊕κ) → ℝ} {A B : Positions ι→ Positions κ}
structure Lives (P : Positions (ι⊕κ) → ℝ) (A : Positions ι→ Positions κ) : Prop where
  analytic : ContDiffAt ℝ ω P 0
  born : ContDiffAt ℝ ω A 0
  zero : A 0=0
  graph : Slope P ∘ curve A =ᶠ[𝓝 0] 0
  rank : (block P 0).det≠0 -- beware decEq, standard Classical forewarn when κ instance locally. At application use all priced inverse with dec.

namespace Lives
lemma curves {x : Positions ι} (h : ContDiffAt ℝ ω P (curve A x)) [hk : DecidableEq κ] (hp : (block P (curve A x)).det≠0)
    (hx : Slope P ∘ curve A =ᶠ[𝓝 x] 0) (ha : ContDiffAt ℝ ω A x) (b : Positions ι) :
    let L := curve A x
    let z := blade (upperCol b) (Slope P) L
    blade b A x = -((block P L)⁻¹ *ᵥ z) := by
  intro L z
  have he := congr_arg (fun l : Positions ι→L[ℝ] Positions κ => l b) (hx.fderiv_eq)
  have HH := along ha; let H := fderiv ℝ (Slope P) L
  have hZ : L = meetVar x (A x) := rfl
  have hP := slope_block (f:=P) (show ContDiffAt ℝ ω P (meetVar x (A x)) from h) -- directional
  have hd := hP.1.differentiableAt (by simp)
  change DifferentiableAt ℝ (Slope P) L at hd
  rw [fderiv_comp _ hd (HH.differentiableAt (by simp)),fderiv_zero] at he
  have hg : blade b (curve A) x=upperCol b + lowerCol (blade b A x) := by
    let S := (partSpace ι κ).symm
    let f (x : Positions ι) := (x,A x)
    change fderiv ℝ (S ∘ f) x b=_
    have hv : fderiv ℝ f x=((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ A x)) := ((hasFDerivAt_id x).prodMk (ha.differentiableAt (by simp)).hasFDerivAt).fderiv
    rw [fderiv_comp _ S.differentiableAt ((show ContDiffAt ℝ ω f x from (contDiffAt_id.prodMk ha)).differentiableAt (by simp)),S.fderiv,hv]
    exact meet_columns ..
  have hl (w : Positions κ) : H (lowerCol w) = block P L *ᵥ w := by
    rw [hZ, ← hP.2]
    have ht := meet_derivative x (A x)
    rw [fderiv_comp _ hd ht.differentiableAt,ht.fderiv]; rfl
  have hv : block P L *ᵥ (blade b A x) = -z := by
    change H (blade b (curve A) x)=0 at he; rw [hg,map_add,add_eq_zero_iff_eq_neg,hl] at he; change _=-H _; rw [he,neg_neg]
  rw [← neg_eq_iff_eq_neg] at hv -- ?
  rw [← hv, Matrix.mulVec_neg,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hp),one_mulVec,neg_neg] -- hv neg orientation

variable (h : Lives P A)
include h

end Lives
-- avoiding top partition price; use inverse in true finite dimension (det invertible on germ)


 -- syntax
end YM.Further.PhysicalPeriodLimitF933.Rainy
