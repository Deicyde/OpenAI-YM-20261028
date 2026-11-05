import YM.Analysis.Polydisc
import YM.Analysis.SmoothJets
import YM.Pressure.Seeds
import YM.Work.F04.Calculus


/-!
# Third and fourth derivatives of the true stationary value

Real, mixed derivatives. Works also in degenerate auxiliary
coordinates (appending frames etc.) -- insert the inverse only later, on coordinates
supporting it. Here `equation` and `exchange` concern ORDINARY mixed derivatives;
no Taylor factorials. The nearest-neighbor plaquette polynomial is not used as a
replacement for the actual germ.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch

open Filter Matrix Work.F04 Tensor Analysis
open scoped Topology ContDiff

section calculus
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

abbrev D2 (f : X → Y) := fderiv ℝ (fderiv ℝ f)
abbrev D3 (f : X → Y) := fderiv ℝ (D2 f)
abbrev D4 (f : X → Y) := fderiv ℝ (D3 f)

theorem D2_jet (f : X → Y) (x u v : X) :
    iteratedFDeriv ℝ 2 f x ![u,v] = D2 f x u v := by
  rw [iteratedFDeriv_two_apply]; rfl

theorem D3_jet (f : X → Y) (x u v w : X) :
    iteratedFDeriv ℝ 3 f x ![u,v,w] = D3 f x u v w := by
  rw [iteratedFDeriv_succ_apply_right]; change iteratedFDeriv ℝ 2 (fderiv ℝ f) x _ w = _
  rw [iteratedFDeriv_two_apply]; rfl

theorem D4_jet (f : X → Y) (x u v w a : X) :
    iteratedFDeriv ℝ 4 f x ![u,v,w,a] = D4 f x u v w a := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_succ_apply_right]; change iteratedFDeriv ℝ 2 (D2 f) x _ w a = _
  rw [iteratedFDeriv_two_apply]; rfl

theorem D_apply {f : X → Y →L[ℝ] Z} {g : X → Y} {x u : X} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    D u (fun y => f y (g y)) x = (f x) (D u g x) + D u f x (g x) := by
  simp only [D, fderiv_clm_apply hf hg, _root_.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

theorem D_left {f : X → Y →L[ℝ] Z} {x u : X} (hf : DifferentiableAt ℝ f x) (v : Y) :
    D u (fun y => f y v) x = D u f x v := by rw [D_apply hf (differentiableAt_const v)]; simp [D]

theorem D_comp {f : Y → Z} {g : X → Y} {x u : X} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) : D u (fun y => f (g y)) x = fderiv ℝ f (g x) (D u g x) := by
  change fderiv ℝ (f ∘ g) x u = _; rw [fderiv_comp x hf hg]; rfl

variable (f : X × Y → ℝ) (b : X → Y) (x : X)

abbrev arc (x : X) := (x,b x)

def tangent (x : X) := (ContinuousLinearMap.id ℝ X).prod (fderiv ℝ b x)

def leg (f : X × Y → ℝ) (z : X × Y) (u v : X × Y) :=
    D3 f z u v ∘L ContinuousLinearMap.inr ℝ X Y

/-- On the real equation, with coarse variable `x` held fixed. Requires only an
actual germ; no uniqueness/global assumptions. Exponential analytic (`ω`) as
in `Critical`. -/
structure OnShell (x : X) : Prop where
  station : vert f ∘ arc b =ᶠ[𝓝 x] fun _ => 0
  path : ContDiffAt ℝ ω b x
  action : ContDiffAt ℝ ω f (arc b x)

namespace OnShell
variable {f b x} (h : OnShell f b x)
include h

theorem arc_smooth : ContDiffAt ℝ ω (arc b) x := contDiffAt_id.prodMk h.path

theorem arc_deriv : fderiv ℝ (arc b) x = tangent b x :=
  ((hasFDerivAt_id x).prodMk (h.path.differentiableAt (by simp)).hasFDerivAt).fderiv

theorem diff_tan (v : X) : DifferentiableAt ℝ (fun y => tangent b y v) x := by
  change DifferentiableAt ℝ (fun y => (v,fderiv ℝ b y v)) x
  exact (differentiableAt_const v).prodMk
    (((h.path.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).clm_apply (differentiableAt_const v))

theorem D_tan (u v : X) : D u (fun y => tangent b y v) x = (0,D2 b x u v) := by
  change fderiv ℝ (fun y => (v,fderiv ℝ b y v)) x u = _
  have hb := (h.path.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  rw [((hasFDerivAt_const _ x).prodMk (hb.clm_apply (differentiableAt_const v)).hasFDerivAt).fderiv]
  change (0,D u (fun y => fderiv ℝ b y v) x) = _
  rw [D_left hb]; rfl

theorem near : ∀ᶠ y in 𝓝 x, OnShell f b y := by
  filter_upwards [eventually_eventuallyEq_nhds.mpr h.station, h.path.eventually (by simp),
    h.arc_smooth.continuousAt.tendsto.eventually (h.action.eventually (by simp))]
    with y h₁ h₂ h₃
  exact ⟨h₁,h₂,h₃⟩

theorem silent (v : Y) : fderiv ℝ f (arc b x) (0,v) = 0 :=
  DFunLike.congr_fun h.station.eq_of_nhds v

theorem flat (u : X) (v : Y) : D2 f (arc b x) (tangent b x u) (0,v) = 0 := by
  have hv := h.station.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp x ((vert_smooth f _ h.action).differentiableAt (by simp))
    (h.arc_smooth.differentiableAt (by simp)), h.arc_deriv, fderiv_const_apply] at hv
  rw [← D2_jet, ← vert_rate f (arc b x) h.action]
  exact DFunLike.congr_fun (DFunLike.congr_fun hv u) v

theorem first (u : X) : fderiv ℝ (f ∘ arc b) x u = fderiv ℝ f (arc b x) (tangent b x u) := by
  rw [fderiv_comp x (h.action.differentiableAt (by simp)) (h.arc_smooth.differentiableAt (by simp)), h.arc_deriv]; rfl

theorem second (u v : X) : D2 (f ∘ arc b) x u v = D2 f (arc b x) (tangent b x u) (tangent b x v) := by
  have hg := h.arc_smooth.differentiableAt (by simp)
  have hb := (((h.action.comp x h.arc_smooth).fderiv_right (m:=ω) (by simp)).differentiableAt (by simp))
  have he := (h.action.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  change D u (fderiv ℝ (f ∘ arc b)) x v = _
  rw [← D_left hb]
  trans D u (fun y => fderiv ℝ f (arc b y) (tangent b y v)) x
  · exact GermD u (h.near.mono fun y hy => hy.first _)
  have he₁ : DifferentiableAt ℝ (fun y => fderiv ℝ f (arc b y)) x := he.comp x hg
  rw [D_apply he₁ (h.diff_tan _), h.D_tan, D_comp he hg, D, h.arc_deriv, h.silent, zero_add]

theorem third (u v w : X) :
    D3 (f ∘ arc b) x u v w = D3 f (arc b x) (tangent b x u) (tangent b x v) (tangent b x w) := by
  have hg := h.arc_smooth.differentiableAt (by simp)
  have hb := ((((h.action.comp x h.arc_smooth).fderiv_right (m:=ω) (by simp)).fderiv_right (m:=ω)
    (by simp)).differentiableAt (by simp))
  have he := ((h.action.fderiv_right (m:=ω) (by simp)).fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  change D u (D2 (f ∘ arc b)) x v w = _
  rw [← D_left hb, ← D_left (hb.clm_apply (differentiableAt_const v))]
  trans D u (fun y => D2 f (arc b y) (tangent b y v) (tangent b y w)) x
  · exact GermD u (h.near.mono fun y hy => hy.second _ _)
  have he₁ : DifferentiableAt ℝ (fun y => D2 f (arc b y)) x := he.comp x hg
  rw [D_apply (he₁.clm_apply (h.diff_tan _)) (h.diff_tan _),
    D_apply he₁ (h.diff_tan _), h.D_tan, h.D_tan, D_comp he hg, D, h.arc_deriv,
    h.flat, zero_add, _root_.add_apply,
    show D2 f (arc b x) (0, D2 b x u v) (tangent b x w) = _ from h.action.isSymmSndFDerivAt_of_omega ..,
    h.flat, zero_add]

/-- The actual mixed second-order stationarity equation. -/
theorem equation (u v : X) (l : Y) :
    D2 f (arc b x) (0,D2 b x u v) (0,l) + leg f (arc b x) (tangent b x u) (tangent b x v) l = 0 := by
  have hg := h.arc_smooth.differentiableAt (by simp)
  have he := ((h.action.fderiv_right (m:=ω) (by simp)).fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  have hm : D u (fun y => D2 f (arc b y) (tangent b y v) (0,l)) x = D u (fun _ : X => (0:ℝ)) x :=
    GermD u (h.near.mono fun y hy => hy.flat v l)
  have he₁ : DifferentiableAt ℝ (fun y => D2 f (arc b y)) x := he.comp x hg
  rw [D_left (he₁.clm_apply (h.diff_tan _)), D_apply he₁ (h.diff_tan _),
    D_comp he hg, h.D_tan, D, h.arc_deriv, D, fderiv_const_apply] at hm
  exact hm

/-- Mixed quartic. Only AFTER cubic residual match should this polynomial (less
all of the output lower action's fourth jet) be completed. -/
theorem exchange (u v w r : X) :
    let z := arc b x; let t := tangent b x
    D4 (f ∘ arc b) x u v w r = D4 f z (t u) (t v) (t w) (t r) +
      leg f z (t w) (t r) (D2 b x u v) + leg f z (t v) (t r) (D2 b x u w) +
      leg f z (t v) (t w) (D2 b x u r) := by
  intro z t
  have hg := h.arc_smooth.differentiableAt (by simp)
  let l : Fin 3 → X := ![v,w,r]
  let V (i : Fin 3) (y : X) := tangent b y (l i)
  have hV (y : X) : (fun i : Fin 3 => V i y) = ![tangent b y v, tangent b y w, tangent b y r] := by
    funext i; fin_cases i <;> rfl
  rw [← D4_jet]
  trans D u (fun y => iteratedFDeriv ℝ 3 f (arc b y) (fun i => V i y)) x
  · have ht := Analysis.cons_jet (j:=3) ((h.action.comp x h.arc_smooth).of_le le_top) u ![v,w,r]
    exact ht.trans <| GermD u <| h.near.mono fun y hy => by
      dsimp only
      rw [hV y,D3_jet,D3_jet,hy.third]
  have hb (i : Fin 3) : DifferentiableAt ℝ (V i) x := h.diff_tan _
  have ha := h.action.differentiableAt_iteratedFDeriv (m:=3) (WithTop.coe_lt_top _)
  have hv : HasFDerivAt (fun y => iteratedFDeriv ℝ 3 f (arc b y)) ((fderiv ℝ (iteratedFDeriv ℝ 3 f) z) ∘L t) x := by
    have e := ha.hasFDerivAt.comp x hg.hasFDerivAt
    rw [h.arc_deriv] at e; exact e
  have hz := (hv.continuousMultilinearMap_apply fun i => (hb i).hasFDerivAt).fderiv
  have hp : fderiv ℝ (iteratedFDeriv ℝ 3 f) z (t u) (fun i => V i x) = D4 f z (t u) (t v) (t w) (t r) := by
    rw [← D4_jet, hV]
    symm; apply iteratedFDeriv_succ_apply_left
  have h₁ (a b c : X × Y) : D3 f z a b c = D3 f z b a c := by
    rw [← D3_jet, ← D3_jet]
    have H := Analysis.sym_Jet (j:=3) (h.action.of_le le_top) ![a,b,c] (Equiv.swap 0 1)
    rw [show ![a,b,c] ∘ Equiv.swap 0 1 = ![b,a,c] by funext i; fin_cases i <;> rfl] at H
    exact H.symm
  have h₂ (a b c : X × Y) : D3 f z a b c = D3 f z a c b := by
    rw [← D3_jet, ← D3_jet]
    have H := Analysis.sym_Jet (j:=3) (h.action.of_le le_top) ![a,b,c] (Equiv.swap 1 2)
    rw [show ![a,b,c] ∘ Equiv.swap 1 2 = ![a,c,b] by funext i; fin_cases i <;> rfl] at H
    exact H.symm
  have hK (i : Fin 3) : fderiv ℝ (V i) x u = (0,D2 b x u (l i)) := h.D_tan _ _
  rw [D,hz]
  simp_rw [_root_.add_apply, _root_.sum_apply, ContinuousLinearMap.comp_apply]
  change fderiv ℝ (iteratedFDeriv ℝ 3 f) z (t u) _ +
    (∑ i : Fin 3, iteratedFDeriv ℝ 3 f z (Function.update _ i (fderiv ℝ (V i) x u))) = _
  rw [hp]
  simp_rw [hV x, hK, Fin.sum_univ_three]
  rw [show Function.update _ (0:Fin 3) (0,D2 b x u (l 0)) = ![(0,D2 b x u v),t w,t r] from ?_,
    show Function.update _ (1:Fin 3) (0,D2 b x u (l 1)) = ![t v,(0,D2 b x u w),t r] from ?_,
    show Function.update _ (2:Fin 3) (0,D2 b x u (l 2)) = ![t v,t w,(0,D2 b x u r)] from ?_]
  · rw [D3_jet,D3_jet,D3_jet,h₁ (0,D2 b x u v), h₂ _ (0,D2 b x u v), h₂ _ (0,D2 b x u w)]
    change _ + (leg f z (t w) (t r) (D2 b x u v) + leg f z (t v) (t r) (D2 b x u w) + leg f z (t v) (t w) (D2 b x u r)) = _
    abel
  all_goals funext i; fin_cases i <;> simp [l,t]
end OnShell
end calculus
end YM.AnalyticNext.QuarticMatch
