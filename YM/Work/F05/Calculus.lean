import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.Bid.Energy



/-!
# Stationary calculus at the real origin

These helpers handle curvature of a composition *at stationarity*,
positivity of the Hessian determinant germ and local uniqueness of
stationary graphs, in normed-space conventions usable for the slices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F05
open Function Filter Set Matrix
open scoped Topology ContDiff Matrix.Norms.Frobenius

variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Curried bilinear form from the second derivative. -/
def bend (F : Y → ℝ) (x : Y) : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ :=
  (fderiv ℝ (fderiv ℝ F) x).toLinearMap₁₂

lemma bend_apply (F : Y → ℝ) (x u v : Y) :
    bend F x u v = iteratedFDeriv ℝ 2 F x ![u,v] := by
  rw [iteratedFDeriv_two_apply]; rfl

lemma bend_congr {F H : Y → ℝ} {x : Y} (he : F =ᶠ[𝓝 x] H) : bend F x = bend H x := by
  ext u v
  simp only [bend_apply, (he.iteratedFDeriv ℝ 2).self_of_nhds]

lemma bend_comp_stationary {F : Y → ℝ} {g : X → Y} {x : X} (hf : ContDiffAt ℝ ω F (g x))
    (hg : ContDiffAt ℝ ω g x) (h : fderiv ℝ F (g x) = 0) :
    bend (F ∘ g) x =
      (bend F (g x)).compl₁₂ (fderiv ℝ g x).toLinearMap (fderiv ℝ g x).toLinearMap := by
  let L := fderiv ℝ F ∘ g
  let D := fderiv ℝ g
  have hw : fderiv ℝ (F ∘ g) =ᶠ[𝓝 x] fun y => (L y).comp (D y) := by
    filter_upwards [hg.eventually (by simp),
      hg.continuousAt.tendsto.eventually (hf.eventually (by simp))] with y hb ha
    exact fderiv_comp y (ha.differentiableAt (by simp)) (hb.differentiableAt (by simp))
  have hf' := (hf.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  have hg' := hg.differentiableAt (by simp)
  have hL := hf'.comp x hg'
  have hD := (hg.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  ext u v
  simp only [bend, ContinuousLinearMap.toLinearMap₁₂_apply, LinearMap.compl₁₂_apply,
    hw.fderiv_eq]
  rw [fderiv_clm_comp (show DifferentiableAt ℝ L x from hL) (show DifferentiableAt ℝ D x from hD),
    show fderiv ℝ L x = (fderiv ℝ (fderiv ℝ F) (g x)).comp (D x) from fderiv_comp _ hf' hg',
    show L x = 0 from h]
  simp only [map_zero, ContinuousLinearMap.zero_comp, zero_add]
  rfl

/-- A partial derivative, still a function on pairs. -/
lemma curve_partial {F : X → Y → Z} (h : ContDiffAt ℝ ω (uncurry F) 0) :
    ContDiffAt ℝ ω (fun z : X × Y => fderiv ℝ (F z.1) z.2) 0 := by
  let H (z : X × Y) := F z.1
  let g := (Prod.snd : X × Y → Y)
  have hs : ContDiffAt ℝ ω (uncurry H) ((0:X × Y),g 0) :=
    h.comp (f:=fun z : (X × Y) × Y => (z.1.1,z.2)) ((0:X × Y),g 0) (by fun_prop)
  exact hs.fderiv (f:=H) (g:=g) contDiffAt_snd (by simp)

section positive
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Analyticity provided in the joint variables. Matrix determinant sign
at zero then persists near both varying arguments. -/
lemma bend_det_pos {F : X → Y → ℝ} (B : Module.Basis ι ℝ Y)
    (h : ContDiffAt ℝ ω (uncurry F) 0) (hp : ∀ y : Y, y≠0 → 0 < bend (F 0) 0 y y) :
    ∀ᶠ z : X × Y in 𝓝 0, 0 < (LinearMap.toMatrix₂ B B (bend (F z.1) z.2)).det := by
  have hf : ContDiffAt ℝ ω (F 0) 0 := h.comp (f:=fun y : Y => ((0:X),y)) 0 (by fun_prop)
  have he : IsSymmSndFDerivAt ℝ (F (0:X)) (0:Y) := hf.isSymmSndFDerivAt_of_omega
  let M (z : X × Y) := LinearMap.toMatrix₂ B B (bend (F z.1) z.2)
  have hm : (M 0).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      change star (M 0 j i) = M 0 i j
      simp only [M, star_trivial, LinearMap.toMatrix₂_apply]
      exact he (B j) (B i)
    intro v hv
    rw [star_trivial]
    have he : v ⬝ᵥ M 0 *ᵥ v = bend (F 0) 0 (B.equivFun.symm v) (B.equivFun.symm v) :=
      dotProduct_toMatrix₂_mulVec B B (bend (F 0) 0) v v
    rw [he]
    apply hp
    intro ht
    apply hv; apply B.equivFun.symm.injective
    rw [ht, map_zero]
  have hh : ContDiffAt ℝ ω
      (fun z : X × Y => fderiv ℝ (fderiv ℝ (F z.1)) z.2) 0 :=
    curve_partial (F:=fun x : X => fderiv ℝ (F x)) (curve_partial h)
  have ht : ContinuousAt M 0 := by
    refine continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j => ?_))
    simp only [M, LinearMap.toMatrix₂_apply, bend, ContinuousLinearMap.toLinearMap₁₂_apply]
    exact (hh.continuousAt.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hc : ContinuousAt (fun z => (M z).det) 0 := continuous_id.matrix_det.continuousAt.comp ht
  exact hc.eventually (lt_mem_nhds hm.det_pos)
end positive

section stationary
variable [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
variable {F : X → Y → ℝ} (h : ContDiffAt ℝ ω (uncurry F) 0)
    (hg : ∀ y : Y, bend (F 0) 0 y y = 0 → y = 0)

include h hg

lemma station_unique {ρ σ : X → Y} (hu : Tendsto ρ (𝓝 0) (𝓝 0))
    (hv : Tendsto σ (𝓝 0) (𝓝 0))
    (hp : ∀ᶠ x in 𝓝 0, fderiv ℝ (F x) (ρ x) = 0)
    (hs : ∀ᶠ x in 𝓝 0, fderiv ℝ (F x) (σ x) = 0) : ρ =ᶠ[𝓝 0] σ := by
  -- triangular IFT at the origin (cf. `Push.authored`); target
  -- has dual second slots here.
  let A (z : X × Y) := fderiv ℝ (F z.1) z.2
  let W (z : X × Y) := (z.1,A z)
  have ha : ContDiffAt ℝ ω A 0 := curve_partial h
  let D := fderiv ℝ A 0
  let T := (ContinuousLinearMap.fst ℝ X Y).prod D
  have he : HasFDerivAt A D 0 := (ha.differentiableAt (by simp)).hasFDerivAt
  have hw : HasFDerivAt W T 0 := hasFDerivAt_fst.prodMk he
  have ht (y : Y) : D (0,y) y = bend (F 0) 0 y y := by
    let P := ContinuousLinearMap.inr ℝ X Y
    have hd : HasFDerivAt A D (P 0) := by rw [map_zero]; exact he
    have hf : HasFDerivAt (fderiv ℝ (F 0)) (D.comp P) 0 := hd.comp (0:Y) P.hasFDerivAt
    simp only [bend, ContinuousLinearMap.toLinearMap₁₂_apply, hf.fderiv]; rfl
  have hi : Injective T := (injective_iff_map_eq_zero _).mpr (fun ⟨x,y⟩ e => by
    have he : x = 0 := congr_arg Prod.fst e
    subst x
    have hy : D (0,y) = 0 := congr_arg Prod.snd e
    rw [hg y (by rw [← ht, hy]; rfl)]; rfl)
  have hq : Module.finrank ℝ (X × Y) = Module.finrank ℝ (X × (Y →L[ℝ] ℝ)) := by
    have he := (LinearMap.toContinuousLinearMap : (Y →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Y →L[ℝ] ℝ)).finrank_eq
    rw [Module.finrank_prod, Module.finrank_prod, ← he, Module.finrank_linearMap_self]
  let R := LinearEquiv.ofBijective T.toLinearMap
    ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hq).mp (show _ from hi)⟩
  let U := LinearEquiv.toContinuousLinearEquiv R
  have hk : HasFDerivAt W (U : X × Y →L[ℝ] X × (Y →L[ℝ] ℝ)) 0 := hw
  have hj : ContDiffAt ℝ ω W 0 := contDiffAt_fst.prodMk ha
  let O := hj.toOpenPartialHomeomorph _ hk (by simp)
  have hb : (0:X × Y) ∈ O.source := ContDiffAt.mem_toOpenPartialHomeomorph_source ..
  have hv' := O.open_source.mem_nhds hb
  have hw' (t : X → Y) (hv : Tendsto t (𝓝 0) (𝓝 0)) : ∀ᶠ x in 𝓝 0, (x,t x)∈O.source :=
    (tendsto_id.prodMk_nhds hv).eventually hv'
  filter_upwards [hw' _ hu,hw' _ hv,hp,hs] with x hx hy hk hl
  have he : O (x,ρ x) = O (x,σ x) := Prod.ext rfl (hk.trans hl.symm)
  exact congr_arg Prod.snd (O.injOn hx hy he)
end stationary
end YM.Work.F05
