import YM.Maxwell.Curls
import YM.Maxwell.Equation

/-!
# One Wick contraction on the actual shell

`legKernel` is bilinear (away origin; value at 0 not used).
Polynomial moments only use different insertions.
TaylorTower uses Taylor coefficients; both left and right. Use extension
of dual on subspace only for an everywhere-function germ convention; prove
independence of BOTH extensions before defining null.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Maxwell
open Function Set Filter
open WaveOn Tensor Analysis
open scoped Topology ContDiff BigOperators

section Paint
variable {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
variable (L : F →L[ℝ] M)

theorem grad_linear {f : E4 → F} {x} (hf : ContDiffAt ℝ ∞ f x) (a) :
    grad a (L ∘ f) x = L (grad a f x) := by
  unfold grad D
  rw [fderiv_comp x L.differentiableAt (hf.differentiableAt (by simp)), L.fderiv]
  rfl

lemma composeColor {U} {f : Field F} (H : WaveOn U f) : WaveOn U (fun a b => L ∘ f a b) := by
  refine ⟨fun _ _ x hx => L.contDiff.contDiffAt.comp x (H.smooth _ _ _ hx),?_,?_,?_⟩
  · intro a b x hx
    nth_rw 1 [Function.comp_apply,H.form a b x hx]
    rw [map_neg]; rfl
  · intro a b c x hx
    rw [grad_linear L (H.smooth _ _ _ hx), grad_linear L (H.smooth _ _ _ hx),
      grad_linear L (H.smooth _ _ _ hx), ← map_add, ← map_add, H.cycle _ _ _ _ hx, map_zero]
  intro b x hx
  have he (a) := grad_linear L (H.smooth a b x hx) a
  simp_rw [he,← map_sum,H.divergence b x hx,map_zero]

lemma superpose {ι : Type*} [Fintype ι] {U} {f : ι → Field F} (H : ∀ i, WaveOn U (f i)) :
    WaveOn U (fun a b x => ∑ i, f i a b x) := by
  have hd (a b c : Axis) (x : E4) (hx : x ∈ U) :
      grad c (fun x : E4 => ∑ i, f i a b x) x = ∑ i, grad c (f i a b) x := by
    unfold grad D
    rw [fderiv_fun_sum (fun i _ => ((H i).smooth a b x hx).differentiableAt (by simp)),sum_apply]
  refine ⟨fun a b x hx => ContDiffAt.sum (fun i _ => (H i).smooth a b x hx), ?_, ?_, ?_⟩
  · intro a b x hx
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => (H i).form a b x hx
  · intro a b c x hx
    rw [hd b c a x hx, hd c a b x hx, hd a b c x hx, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => (H i).cycle a b c x hx
  intro b x hx
  simp_rw [show ∀ a, grad a (fun x => ∑ i, f i a b x) x = _ from fun a => hd a b a x hx]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun i _ => (H i).divergence b x hx
end Paint

variable {G : Gauge} {j l : ℕ}
abbrev Probe (G : Gauge) (j : ℕ) := Shell G j →ₗ[ℝ] ℝ
abbrev Extended (G : Gauge) (j : ℕ) := TwoJet G.Color j →ₗ[ℝ] ℝ

def extension (p : Probe G j) : Extended G j := p ∘ₗ (onShell _ _).subtype.leftInverse

def constrain (P : TwoJet G.Color j →ₗ[ℝ] ℝ) : Probe G j := P.comp (onShell _ _).subtype

theorem genuine (p : Probe G j) : constrain (extension p) = p := by
  ext x
  exact congr_arg p (LinearMap.leftInverse_apply_of_inj (onShell G.Color j).ker_subtype x)

def unitColor (G : Gauge) (i : G.ColorIndex) : G.Color := EuclideanSpace.single i 1

def tint (v : G.Color) : ℝ →L[ℝ] G.Color := (ContinuousLinearMap.id ℝ ℝ).smulRight v

theorem tint_at (v : G.Color) (t : ℝ) : tint v t = t • v := rfl

def leftF (G : Gauge) (c : G.ColorIndex) (i l : Axis) : Field G.Color := fun a b =>
  tint (G := G) (unitColor G c) ∘ bareCurl a b i l

theorem left_eq (c : G.ColorIndex) (i l : Axis) : WaveOn away (leftF G c i l) :=
  composeColor _ (Bare.equation ..)

theorem for_right (c : G.ColorIndex) (i l : Axis) : WaveOn away (fun a b => leftF G c a b i l) :=
  composeColor _ (Bare.equation_right ..)

def scalarTest (P : Extended G j) (c : G.ColorIndex) : Field ℝ := fun i l =>
  P ∘ nth (leftF G c i l) j

lemma test_mem (P : Extended G j) (c : G.ColorIndex) : WaveOn away (scalarTest P c) := by
  let V (i l) := leftF G c i l
  let A : Axis → Axis → E4 → TwoJet G.Color j := fun i l => nth (V i l) j
  let L := P.toContinuousLinearMap
  change WaveOn away (fun i l => L ∘ A i l)
  have he (i l) (x) (hx : x ≠ 0) : ContDiffAt ℝ ∞ (A i l) x :=
    (left_eq c i l).nth_smooth hx
  have hw (α β i l : Axis) (x : E4) (hx : x ≠ 0) (a : Axis) :
      grad a (A i l) x α β = coeff (grad a (V i l α β)) j x := by
    have hf := he i l x hx
    let E1 := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Axis => Axis → T E4 G.Color j) α
    let E2 := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Axis => T E4 G.Color j) β
    change E2.comp E1 (grad a (A i l) x) = _
    rw [← grad_linear (E2.comp E1) hf]
    exact D_coeff (((left_eq c i l).smooth α β x hx).of_le (WithTop.coe_le_coe.mpr le_top)) (basis a)
  have hp (α β a i l : Axis) (x : E4) (hx : x ≠ 0) : ContDiffAt ℝ j (grad a (V i l α β)) x :=
    (grad_smooth a ((left_eq c i l).smooth α β x hx) (m := ∞) (by simp)).of_le (WithTop.coe_le_coe.mpr le_top)
  apply composeColor
  refine ⟨he,?_,?_,?_⟩
  · intro i l x hx
    ext1 α; ext1 β
    change coeff _ _ _ = -coeff _ _ _
    rw [← neg_coeff]; refine GermCoeff j ?_
    filter_upwards [open_away.mem_nhds hx] with y hy
    exact (for_right c α β).form i l y hy
  · intro a b d x hx
    funext α β
    simp only [Pi.add_apply,hw _ _ _ _ _ hx,Pi.zero_apply]
    rw [← coeff_add (hp _ _ _ _ _ _ hx) (hp _ _ _ _ _ _ hx), ← coeff_add
      (show ContDiffAt ℝ j (grad a (V b d α β) + grad b (V d a α β)) x from (hp _ _ _ _ _ _ hx).add (hp _ _ _ _ _ _ hx))
      (hp _ _ _ _ _ _ hx)]
    rw [← coeff_zero j x]; refine GermCoeff _ ?_
    filter_upwards [open_away.mem_nhds hx] with y hy; exact (for_right c α β).cycle a b d y hy
  intro b x hx
  funext α β
  simp_rw [Finset.sum_apply, hw _ _ _ _ _ hx]
  rw [← coeff_sum]
  · have ht : ∑ a : Axis, grad a (V a b α β) =ᶠ[𝓝 x] (fun _ => (0:G.Color)) := by
      filter_upwards [open_away.mem_nhds hx] with y hy
      rw [Finset.sum_apply]; exact (for_right c α β).divergence b y hy
    exact (GermCoeff j ht).trans (coeff_zero j x)
  exact fun i _ => hp _ _ _ _ _ _ hx

/-- The left functional applied to the Taylor coefficients at x leaves
color-valued germ indexed by the right k,m. Variable is still z=x-y. -/
def responded (G : Gauge) {j : ℕ} (P : Extended G j) : Field G.Color := fun i l z =>
  ∑ c, scalarTest (G := G) P c i l z • unitColor G c

theorem response (P : Extended G j) : WaveOn away (responded G P) :=
  superpose fun c => composeColor (tint (G := G) (unitColor G c)) (test_mem (G := G) P c)

/-- One-leg pairing with unconstrained functionals first. -/
def contraction (G : Gauge) {j l : ℕ} (P : Extended G j) (Q : Extended G l) (z : E4) : ℝ :=
  (-1)^l * Q (nth (responded G P) l z)

theorem descends {P P' : Extended G j} {Q Q' : Extended G l} (hp : constrain (G := G) P = constrain P')
    (hq : constrain (G := G) Q = constrain Q') {z : E4} (hz : z ≠ 0) :
    contraction G P Q z = contraction G P' Q' z := by
  have ht (i m : Axis) : responded G P i m =ᶠ[𝓝 z] responded G P' i m := by
    filter_upwards [open_away.mem_nhds (show z ∈ away from hz)] with y hy
    unfold responded
    exact Finset.sum_congr rfl fun c _ => congr_arg (fun x : ℝ => x • unitColor G c)
      (LinearMap.congr_fun hp ⟨_,(left_eq c i m).jets open_away hy⟩)
  unfold contraction
  rw [show nth (responded G P) l z = nth (responded G P') l z from funext fun i => funext fun k => GermCoeff l (ht i k)]
  exact congr_arg (fun x : ℝ => (-1 : ℝ)^l * x)
    (LinearMap.congr_fun hq ⟨_, (response (G := G) P').jets open_away hz⟩)

def legKernel (p : Probe G j) (q : Probe G l) (z : E4) : ℝ :=
  contraction G (extension p) (extension q) z

theorem concrete (P : Extended G j) (Q : Extended G l) {x} (hx : x ≠ 0) :
    legKernel (constrain (G := G) P) (constrain Q) x = contraction G P Q x :=
  descends (genuine _) (genuine _) hx

theorem kernel_smooth (p : Probe G j) (q : Probe G l) {x} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (legKernel p q) x := by
  let L := (extension q).toContinuousLinearMap
  refine contDiffAt_const.mul ?_
  exact L.contDiff.contDiffAt.comp x ((response (G := G) (extension p)).nth_smooth hx)

end YM.Maxwell
