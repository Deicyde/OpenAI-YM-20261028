import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.Dual




/-!
# Analytic stationarity

Used in small-torus stationary, frame charts and near-flat loop. Gives no
uniform radius for `L`, period or prior history. `∃` means genuine
`Classical.choose` route from real germ premises (complex extension
bookkeeping separate).
-/
noncomputable section
namespace YM.Analytic
open Filter Topology Set InnerProductSpace
open scoped InnerProductSpace

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] 

/-- Gradient covector with first argument B frozen. -/
def slope (f : E × F → ℝ) (x : E × F) :=
  (fderiv ℝ f x).comp (ContinuousLinearMap.inr ℝ E F)

protected theorem sliceDrv (f : E × F → ℝ) (x : E × F) (hd : DifferentiableAt ℝ f x) :
    HasFDerivAt (fun b => f (x.1,b)) (slope f x) x.2 := HasFDerivAt.comp x.2 hd.hasFDerivAt
      (hasFDerivAt_const x.1 x.2 |>.prodMk (hasFDerivAt_id x.2))

protected theorem slope_hol (f : E × F → ℝ) (x : E × F) (h : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (slope f) x := by
  let L : ((E × F) →L[ℝ] ℝ) →L[ℝ] StrongDual ℝ F :=
    (ContinuousLinearMap.compL ℝ F (E × F) ℝ).flip (ContinuousLinearMap.inr ℝ E F)
  exact (L.analyticAt _).comp h.fderiv

/-- Even near nonzero backgrounds. -/
theorem slope_prime (f : E × F → ℝ) (a : E × F) (h : AnalyticAt ℝ f a) (v w : F) :
    fderiv ℝ (slope f) a (0,v) w = iteratedFDeriv ℝ 2 (fun q => f (a.1,q)) a.2 ![v,w] := by
  let T := fun q : F => (a.1, q)
  have H : HasFDerivAt (slope f ∘ T) ((fderiv ℝ (slope f) a).comp (ContinuousLinearMap.inr ℝ E F)) a.2 := by
    have he : HasFDerivAt T (ContinuousLinearMap.inr ℝ E F) a.2 := (hasFDerivAt_const ..).prodMk (hasFDerivAt_id ..)
    exact HasFDerivAt.comp a.2 (Analytic.slope_hol f a h).differentiableAt.hasFDerivAt he
  have eq : fderiv ℝ (fun q => f (a.1,q)) =ᶠ[𝓝 a.2] slope f ∘ T := by
    have he : Tendsto T (𝓝 a.2) (𝓝 a) := ((continuous_const (y := a.1)).prodMk continuous_id).continuousAt
    filter_upwards [he.eventually h.eventually_analyticAt] with x hx
    exact (Analytic.sliceDrv f _ hx.differentiableAt).fderiv
  rw [iteratedFDeriv_two_apply, (H.congr_of_eventuallyEq eq).fderiv]; simp [ContinuousLinearMap.inr_apply]

variable [CompleteSpace F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- `param` qualitative step. -/
theorem param (f : E × F → ℝ) (x : E × F) (h : AnalyticAt ℝ f x)
    (hc : HasFDerivAt (fun b => f (x.1,b)) (0 : F →L[ℝ] ℝ) x.2)
    (hp : ∀ v : F, v ≠ 0 → 0 < iteratedFDeriv ℝ 2 (fun b => f (x.1,b)) x.2 ![v,v]) :
    ∃ g : E → F, g x.1 = x.2 ∧ AnalyticAt ℝ g x.1 ∧
      ∀ᶠ a in 𝓝 x.1, HasFDerivAt (fun b => f (a,b)) (0 : F →L[ℝ] ℝ) (g a) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let R : (StrongDual ℝ F) ≃L[ℝ] F := (toDual ℝ F).symm.toContinuousLinearEquiv
  let k : E × F → E × F := fun p => (p.1, R (slope f p))
  have hfst : AnalyticAt ℝ Prod.fst (x : E × F) := (ContinuousLinearMap.fst ℝ E F).analyticAt _
  have hk : AnalyticAt ℝ k x := hfst.prod ((R.analyticAt _).comp (Analytic.slope_hol _ _ h))
  let d := fderiv ℝ k x
  have Hd : Function.Injective d := by
    apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨p,q⟩ hm
    let m := fderiv ℝ (slope f) x
    have He : HasFDerivAt k ((ContinuousLinearMap.fst ℝ E F).prod
        (R.toContinuousLinearMap.comp m)) x := HasFDerivAt.prodMk hasFDerivAt_fst
          ((R.toContinuousLinearMap.hasFDerivAt).comp x (Analytic.slope_hol _ _ h).differentiableAt.hasFDerivAt)
    unfold d at hm; rw [He.fderiv] at hm
    have ha : p = 0 := congrArg Prod.fst hm
    subst p
    have he : R (m (0, q)) = 0 := congrArg Prod.snd hm
    rw [map_eq_zero_iff R R.injective] at he
    have hq : q = 0 := by
      by_contra Hq
      have hq := hp q Hq
      rw [← slope_prime f x h q q] at hq
      change 0 < m _ _ at hq
      simp [he] at hq
    subst q; rfl
  let e : (E × F) ≃L[ℝ] E × F := LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective d.toLinearMap ⟨Hd, LinearMap.surjective_of_injective Hd⟩)
  have hD : fderiv ℝ k x = e.toContinuousLinearMap := by ext <;> rfl
  have hK : HasStrictFDerivAt k (e : _ →L[ℝ] E × F) x := hD ▸ hk.hasStrictFDerivAt
  let K := hK.toOpenPartialHomeomorph k
  have hx : k x = (x.1,0) := by
    have hv : slope f x = 0 := ((Analytic.sliceDrv f x h.differentiableAt).unique hc)
    simp [k,hv]
  have hsrc : x ∈ K.source := hK.mem_toOpenPartialHomeomorph_source
  have A : AnalyticAt ℝ K.symm (x.1,0) := by
    rw [← hx]; exact K.analyticAt_symm' (i := e) hsrc hk hD
  have hs : K.symm (x.1,0) = x := hx ▸ K.left_inv hsrc
  let g : E → F := fun a => (K.symm (a,0)).2
  have ha : AnalyticAt ℝ g x.1 := AnalyticAt.comp (g := @Prod.snd E F) (by
    exact (ContinuousLinearMap.snd ℝ E F).analyticAt _) <|
    AnalyticAt.comp (f := fun a : E => (a,(0:F))) A (analyticAt_id.prod analyticAt_const)
  refine ⟨g, congrArg Prod.snd hs, ha, ?_⟩
  have ha' : ∀ᶠ a : E in 𝓝 x.1, (a,(0:F)) ∈ K.target := by
    apply ContinuousAt.preimage_mem_nhds (continuous_id.prodMk continuous_const).continuousAt
    exact K.open_target.mem_nhds (hx ▸ K.map_source hsrc)
  have hat : Tendsto (fun a : E => K.symm (a,(0:F))) (𝓝 x.1) (𝓝 x) := by
    nth_rw 2 [← hs]
    exact A.continuousAt.comp (f := fun a => (a,(0:F))) (by fun_prop)
  filter_upwards [ha',hat.eventually h.eventually_analyticAt] with a ha' hk'
  let y := K.symm (a,(0:F))
  have h1 : k y = (a,0) := K.right_inv ha'
  have H : slope f y = 0 := R.injective <| by rw [map_zero]; exact congrArg Prod.snd h1
  have Hv := Analytic.sliceDrv f y hk'.differentiableAt
  rw [H,show y.1=a from congrArg Prod.fst h1] at Hv
  exact Hv
end YM.Analytic
