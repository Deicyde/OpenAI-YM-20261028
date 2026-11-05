import YM.Analytic.Implicit
import YM.Push.STATIONARY_UNIFORM.Calculus



/-!
# Real estimates for Hilbert vertical coordinates

Use for the frame scores in counting. DO NOT apply directly with Pi norms
and conclude a uniform receipt in another norm!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Filter Function Set Metric
open YM.Analytic
open scoped Topology ContDiff BigOperators

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E × F → ℝ} {c m R : ℝ}

-- name collision slope mathlib

section Slope

def vertical (f : E × F → ℝ) (z : E × F) :=
  (fderiv ℝ (YM.Analytic.slope f) z).comp (ContinuousLinearMap.inr ℝ E F)

lemma allows_slope {n : ℕ} {p : E × F} (h : Allows (n+1) f p c) :
    Allows n (YM.Analytic.slope f) p c := by
  let L := ContinuousLinearMap.inr ℝ E F
  let K := (ContinuousLinearMap.compL ℝ F (E × F) ℝ).flip L
  have hf : Allows n (fderiv ℝ f) p c := by
    refine ⟨h.analytic.fderiv_right (by simp), fun k hk => ?_⟩
    rw [norm_iteratedFDeriv_fderiv]; exact h.norm_le _ (Nat.succ_le_succ hk)
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun x => by simp [L])
  have hK : ‖K‖ ≤ 1 := K.opNorm_le_bound zero_le_one fun x => by
    change ‖x ∘L L‖ ≤ _
    rw [one_mul]; exact (x.opNorm_comp_le L).trans (mul_le_of_le_one_right (norm_nonneg x) hL)
  have ht := Allows.linear K hf hK
  rw [one_mul] at ht; exact ht

lemma vert_near (hR : 0<R) (hb : ∀ x∈ball (0:E × F) R, Allows 3 f x m) {x : E × F} (hx : x∈ball 0 R) :
    ‖vertical f x - vertical f 0‖ ≤ m * R := by
  have hh (x : E × F) (hx : x∈ball (0:E × F) R) : Allows 2 (YM.Analytic.slope f) x m := allows_slope (hb x hx)
  have hv (x : E × F) (hx : x∈ball (0:E × F) R) := (hh x hx).analytic.fderiv_right (m:=ω) (by simp)
  let g := fderiv ℝ (YM.Analytic.slope f)
  have he := (convex_ball (0:E × F) R).norm_image_sub_le_of_norm_fderiv_le (f:=g)
    (fun i hi => (hv i hi).differentiableAt (by simp)) (C:=m) (fun i hi => by
      rw [← norm_iteratedFDeriv_one g]
      change ‖iteratedFDeriv ℝ 1 (fderiv ℝ (YM.Analytic.slope f)) i‖ ≤ m
      rw [norm_iteratedFDeriv_fderiv]; exact (hh i hi).norm_le _ le_rfl) (mem_ball_self hR) hx
  rw [sub_zero] at he
  let L := ContinuousLinearMap.inr ℝ E F
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun x => by simp [L])
  have hed : vertical f x - vertical f 0 = (g x-g 0).comp L := by ext; rfl
  rw [hed]; apply ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hL)).trans
  exact he.trans (mul_le_mul_of_nonneg_left (show ‖x‖ < R by simpa using hx).le (hh x hx).nonneg)

def Strong (f : E × F → ℝ) (x : E × F) (c : ℝ) := ∀ v : F, c*‖v‖^2 ≤ vertical f x v v

lemma Strong.invert {x : E × F} (h : Strong f x c) (v : F) : c*‖v‖ ≤ ‖vertical f x v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  apply le_of_mul_le_mul_right _ (norm_pos_iff.mpr hv)
  rw [mul_assoc, ← sq]
  exact (h v).trans ((le_abs_self _).trans ((vertical f x v).le_opNorm v))



lemma Strong.near (hc : Strong f 0 c) (hR : 0<R) (hb : ∀ x∈ball (0:E × F) R, Allows 3 f x m)
    {x : E × F} (hx : x∈ball 0 R) : Strong f x (c-m*R) := by
  intro v
  let L := vertical f 0 - vertical f x
  have h : ‖L‖ ≤ m * R := by rw [show ‖L‖ = _ from norm_sub_rev (vertical f 0) (vertical f x)]; exact vert_near hR hb hx
  have hh : L v v ≤ (m * R)*‖v‖^2 := calc
    _ ≤ ‖L v‖ * ‖v‖ := (le_abs_self _).trans ((L v).le_opNorm _)
    _ ≤ (m*R)*‖v‖ * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring
  change vertical f 0 v v - vertical f x v v ≤ _ at hh
  linarith [hc v]

lemma Strong.unique (hc : Strong f 0 c) (hR : 0<R) (hb : ∀ x∈ball (0:E × F) R, Allows 3 f x m)
    (hm : m*R < c) {x : E} (hx : x∈ ball 0 R) {v w : F} (hv : v∈ball 0 R) (hw : w∈ball 0 R)
    (he : YM.Analytic.slope f (x,v)=YM.Analytic.slope f (x,w)) : v=w := by
  let s (b : F) := YM.Analytic.slope f (x,b)
  have hi (b : F) (hh : b∈ball 0 R) : (x,b)∈ball (0:E × F) R := by
    simpa [Prod.norm_def] using And.intro (show ‖x‖<R by simpa using hx) (show ‖b‖<R by simpa using hh)
  have h (b : F) (hh : b∈ball 0 R) : HasFDerivAt s (vertical f (x,b)) b := by
    refine HasFDerivAt.comp (𝕜 := ℝ) (g:=YM.Analytic.slope f) (f:=fun y : F => (x,y)) b ?_ ?_
    · exact ((allows_slope (n:=2) (hb _ (hi _ hh))).analytic.differentiableAt (by simp)).hasFDerivAt
    exact (hasFDerivAt_const x b).prodMk (hasFDerivAt_id b)
  have hz := (convex_ball (0:F) R).norm_image_sub_le_of_norm_fderiv_le' (f:=s) (φ:=vertical f 0) (C:=m*R)
    (fun b hh => (h _ hh).differentiableAt)
    (fun b hh => by rw [(h _ hh).fderiv]; exact vert_near hR hb (hi _ hh)) hv hw
  rw [show s w=s v from he.symm, sub_self, zero_sub, norm_neg] at hz
  by_contra hne
  exact (mul_lt_mul_of_pos_right hm (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne)))).not_ge ((hc.invert _).trans hz)
end Slope
end YM.Push.Uniform
