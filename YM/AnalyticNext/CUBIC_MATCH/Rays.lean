import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import YM.Analysis.Homogeneous
import YM.Analysis.Polydisc
import YM.Pressure.Rows




set_option warningAsError false

/-!
# Terms on real curves

Helpers for retaining actual Taylor jets, with the coefficient convention
of E (`1/k!`). We'll use these on real germ substitutions; we won't infer
any analytic width from the Taylor matching in this file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch

open Filter Function
open scoped ContDiff Topology BigOperators

variable {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {k : ℕ}

/-- Terms of the path tested at the origin of its real parameter. -/
def term (k : ℕ) (g : ℝ → E) := (k.factorial : ℝ)⁻¹ • iteratedDeriv k g 0

@[simp] lemma term_zero (g : ℝ → E) : term 0 g = g 0 := by simp [term]
@[simp] lemma term_one (g : ℝ → E) : term 1 g = deriv g 0 := by simp [term]

lemma term_congr {g h : ℝ → E} (e : g =ᶠ[𝓝 0] h) : term k g = term k h := by
  unfold term
  rw [e.iteratedDeriv_eq k]

lemma term_linear (L : E →L[ℝ] F) {g : ℝ → E} (e : ContDiffAt ℝ k g 0) :
    term k (fun t => L (g t)) = L (term k g) := by
  unfold term
  rw [map_smul, iteratedDeriv, show (fun t => L (g t)) = L ∘ g from rfl,
    L.iteratedFDeriv_comp_left e le_rfl]
  rfl

lemma term_add {g h : ℝ → E} (p : ContDiffAt ℝ k g 0) (q : ContDiffAt ℝ k h 0) :
    term k (fun t => g t + h t) = term k g + term k h := by
  unfold term; rw [show (fun t => g t + h t) = g+h from rfl, iteratedDeriv_add p q, smul_add]

lemma term_sub {g h : ℝ → E} (p : ContDiffAt ℝ k g 0) (q : ContDiffAt ℝ k h 0) :
    term k (fun t => g t - h t) = term k g - term k h := by
  unfold term; rw [show (fun t => g t - h t) = g-h from rfl, iteratedDeriv_sub p q, smul_sub]

lemma term_sum {ι : Type*} {s : Finset ι} {g : ι → ℝ → E}
    (p : ∀ i∈s, ContDiffAt ℝ k (g i) 0) :
    term k (fun t => ∑ i∈s, g i t) = ∑ i∈s, term k (g i) := by
  unfold term; rw [iteratedDeriv_fun_sum p, Finset.smul_sum]



/-- Localize the linear pullback to an actual germ. -/
lemma jet_comp_linear {f : E → F} (L : Z →L[ℝ] E) {z : Z} (p : ContDiffAt ℝ k f (L z)) :
    iteratedFDeriv ℝ k (f ∘ L) z =
      (iteratedFDeriv ℝ k f (L z)).compContinuousLinearMap fun _ => L := by
  obtain ⟨s,hs,hu⟩ := p.contDiffOn (m := ↑k) le_rfl (by simp)
  obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp hs
  have he := Metric.isOpen_ball (x := L z) (ε := r)
  have hz := Metric.mem_ball_self (x := L z) hr
  have h := he.preimage L.continuous
  have hh := L.iteratedFDerivWithin_comp_right (hu.mono hb) he.uniqueDiffOn h.uniqueDiffOn hz (i := k) le_rfl
  rwa [iteratedFDerivWithin_of_isOpen _ he hz,
    iteratedFDerivWithin_of_isOpen _ h (Set.mem_preimage.mpr hz)] at hh

lemma term_ray {f : E → F} (p : ContDiffAt ℝ k f 0) (x : E) :
    term k (fun t : ℝ => f (t • x)) = Tensor.diagonal (Tensor.coeff f k 0) x := by
  let L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x
  have h1 : L (1:ℝ)=x := one_smul _ _
  unfold term
  change _ • (iteratedFDeriv ℝ k (f ∘ L) 0 fun _ => 1) = _
  rw [jet_comp_linear L (show ContDiffAt ℝ k f (L 0) by rw [map_zero]; exact p), map_zero]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,h1]; rfl

/-- No acceleration terms from either function when comparing cubic of a residual whose
slope and Hessian vanish. -/
lemma term_three_of_lowNull {f : E → F} {a : ℝ → E} (he : a 0 = 0)
    (p : ContDiffAt ℝ 3 f 0) (q : ContDiffAt ℝ 3 a 0) (p₁ : fderiv ℝ f 0 = 0)
    (p₂ : iteratedFDeriv ℝ 2 f 0 = 0) :
    term 3 (f ∘ a) = Tensor.diagonal (Tensor.coeff f 3 0) (deriv a 0) := by
  rw [term, iteratedDeriv_vcomp_three (f:=a) (g:=f) (by rw [he]; exact p) q,
    he, p₁, p₂]
  simp only [smul_zero,
    zero_apply, add_zero]; rfl







end YM.CubicMatch
