import YM.Pressure.Rows

/-!
# IFT helpers for real germs at actual branch. Fixed parameters here,
no claim on width. Strong coordinate derivative at an ALL-min criterion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push
open Function Set Filter NormedSpace
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace X] [CompleteSpace Y]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

omit [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
lemma side (g : X → Y) (h : DifferentiableAt ℝ g (0:X)) (x : X) :
    HasDerivAt (fun t : ℝ => g (t • x)) (fderiv ℝ g 0 x) 0 := by
  let Q : ℝ → X := (· • x)
  have hh : HasDerivAt Q x 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const x
  have he := h.hasFDerivAt
  rw [show (0:X) = Q 0 by simp [Q]] at he
  simpa only [Q,zero_smul] using! he.comp_hasDerivAt 0 hh

lemma authored (f : X → Y) (F : X × Y → Y) (b : Y) (H : ∀ᶠ x in 𝓝 0,F (x,f x)=b) (hv : ContinuousAt f 0)
    (he : ContDiffAt ℝ ω F (0,f 0)) (hx : ∀ v : Y, fderiv ℝ F (0,f 0) (0,v)=0 → v=0) : ContDiffAt ℝ ω f 0 := by
  let g (x : X×Y) := (x.1,F x)
  let a : X × Y := (0, f 0)
  let G := (ContinuousLinearMap.fst ℝ X Y).prod (fderiv ℝ F a)
  have hg : HasFDerivAt g G a := hasFDerivAt_fst.prodMk (he.differentiableAt (by simp)).hasFDerivAt
  have h : Injective G := (injective_iff_map_eq_zero _).mpr (fun v e => by
    rcases v with ⟨x,y⟩
    have he : x=0 := congr_arg Prod.fst e
    subst x; rw [hx y (congr_arg Prod.snd e)]; rfl)
  let T := LinearEquiv.ofBijective G.toLinearMap ⟨h,LinearMap.injective_iff_surjective.mp (show _ from h)⟩
  let B := LinearEquiv.toContinuousLinearEquiv T
  have heQ : HasFDerivAt g (B : (X×Y) →L[ℝ] X×Y) a := hg
  have hF : ContDiffAt ℝ ω g a := contDiffAt_fst.prodMk he
  let E := hF.toOpenPartialHomeomorph _ heQ (by simp)
  have ha : a∈E.source:=ContDiffAt.mem_toOpenPartialHomeomorph_source ..
  have hh : ContDiffAt ℝ ω (E.symm) (g a) := hF.to_localInverse heQ (by simp)
  have hk : ContDiffAt ℝ ω (fun c : X×Y => (E.symm c).2) (0,b) := by
    rw [show (0,b)=g a from Prod.ext rfl (mem_of_mem_nhds H).symm]
    exact contDiffAt_snd.comp _ hh
  refine (show ContDiffAt ℝ ω (fun x : X => (E.symm (x,b)).2) 0 from ContDiffAt.comp (f:=fun x => (x,b)) 0 hk (contDiffAt_id.prodMk contDiffAt_const)).congr_of_eventuallyEq ?_
  have hy := (tendsto_id (x:=𝓝 (0:X))).prodMk_nhds hv.tendsto
  filter_upwards [hy.eventually (E.open_source.mem_nhds ha),H] with i hi h
  rw [show E.symm (i,b)=(i,f i) by rw [show (i,b)=g (i,f i) from Prod.ext rfl h.symm]; exact E.left_inv hi]
end YM.Push
