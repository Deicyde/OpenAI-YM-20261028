import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.PCalc.Band



/-! Real germ calculus tools for the fixed-period solve. -/

set_option autoImplicit false
noncomputable section

open Filter Function Matrix
open scoped Topology ContDiff

namespace YM.Work.F04

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Vertical differential, agreeing with the partial derivative at smooth points. -/
def vert (F : X × Y → ℝ) (z : X × Y) : Y →L[ℝ] ℝ :=
  fderiv ℝ F z ∘L ContinuousLinearMap.inr ℝ X Y

lemma hasFDerivAt_slice (F : X × Y → ℝ) (x : X) (y : Y)
    (hd : DifferentiableAt ℝ F (x, y)) :
    HasFDerivAt (fun v => F (x, v)) (vert F (x, y)) y := by
  have he : HasFDerivAt (fun v => (x, v)) (ContinuousLinearMap.inr ℝ X Y) y :=
    (hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)
  exact hd.hasFDerivAt.comp y he

lemma vert_smooth (F : X × Y → ℝ) (z : X × Y) (hf : ContDiffAt ℝ ω F z) :
    ContDiffAt ℝ ω (vert F) z :=
  (hf.fderiv_right (m := ω) (by simp)).clm_comp contDiffAt_const

lemma vert_rate (F : X × Y → ℝ) (z : X × Y) (hf : ContDiffAt ℝ ω F z)
    (w : X × Y) (v : Y) :
    fderiv ℝ (vert F) z w v = iteratedFDeriv ℝ 2 F z ![w, (0, v)] := by
  have hh := ((hf.fderiv_right (m := ω) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.inr ℝ X Y) z)
  rw [show fderiv ℝ (vert F) z = _ from hh.fderiv, iteratedFDeriv_two_apply]
  simp

/-- At a stationary point the second derivative on pullback has no second
chain-rule summand from the inner map. -/
lemma stationary_chain (F : Y → ℝ) (W : X → Y) (x : X) (hg : ContDiffAt ℝ ω F (W x))
    (hh : ContDiffAt ℝ ω W x) (he : fderiv ℝ F (W x) = 0) (a b : X) :
    fderiv ℝ (fderiv ℝ (F ∘ W)) x a b =
      iteratedFDeriv ℝ 2 F (W x) ![fderiv ℝ W x a, fderiv ℝ W x b] := by
  have H : fderiv ℝ (F ∘ W) =ᶠ[𝓝 x] fun y => fderiv ℝ F (W y) ∘L fderiv ℝ W y := by
    filter_upwards [hh.eventually (by simp),
      hh.continuousAt.tendsto.eventually (hg.eventually (by simp))] with y hy hz
    exact fderiv_comp y (hz.differentiableAt (by simp)) (hy.differentiableAt (by simp))
  have hx := (hg.fderiv_right (m := ω) (by simp)).differentiableAt (by simp)
  have hw := hh.differentiableAt (by simp)
  have hh' := (hh.fderiv_right (m := ω) (by simp)).differentiableAt (by simp)
  have hd := (hx.hasFDerivAt.comp x hw.hasFDerivAt).clm_comp hh'.hasFDerivAt
  rw [H.fderiv_eq, show fderiv ℝ (fun y => fderiv ℝ F (W y) ∘L fderiv ℝ W y) x = _ from hd.fderiv,
    iteratedFDeriv_two_apply]
  simp [he]

/-- Recognise the quadratic part from just the Hessian of a smooth real germ. -/
lemma half_pairing (F : X → ℝ) (hf : ContDiffAt ℝ ω F 0) :
    Precision.SameJet 2 F (fun x : X => (1/2:ℝ) * (fderiv ℝ (fderiv ℝ F) 0 x x)) := by
  let Q := fderiv ℝ (fderiv ℝ F) 0
  have hs (a b : X) : Q a b = Q b a := hf.isSymmSndFDerivAt (by simp) a b
  change Precision.SameJet 2 F (fun x => (1/2:ℝ) * Q x x)
  have hd (x : X) : HasFDerivAt (fun y => (1/2:ℝ) * Q y y) (Q x) x := by
    have hh := (Q.hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)
    convert! hh.const_smul (1/2:ℝ) using 1
    ext y
    simp [smul_eq_mul, hs y x]
    ring
  have he : fderiv ℝ (fun x => (1/2:ℝ) * Q x x) = Q := funext fun x => (hd x).fderiv
  refine ⟨hf, ?_, ?_⟩
  · apply ContDiffAt.mul contDiffAt_const
    exact Q.contDiff.contDiffAt.clm_apply contDiffAt_id
  ext v
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, he, Q.fderiv]

lemma form_invertible [FiniteDimensional ℝ Y] (Q : Y →L[ℝ] Y →L[ℝ] ℝ) (hi : Injective Q) :
    Q.IsInvertible := by
  have hf : Module.finrank ℝ Y = Module.finrank ℝ (Y →L[ℝ] ℝ) := calc
    _ = Module.finrank ℝ (Y →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
    _ = _ := LinearMap.toContinuousLinearMap.finrank_eq
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hf).mp
    (show Injective Q.toLinearMap from hi)
  exact ⟨(LinearEquiv.ofBijective Q.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

end YM.Work.F04
