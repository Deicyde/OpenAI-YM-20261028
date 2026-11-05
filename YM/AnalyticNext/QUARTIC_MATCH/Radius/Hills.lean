import YM.AnalyticNext.QUARTIC_MATCH.Radius.Warp

/-!
# Room in the no-hole Hessian -- background dependence at post-L

First absolute row and gradient derivative bounds. For all trees, unused choices too. We work with
orientation genuine; not promising clipped no-hole estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open Purchase Articles Showroom Model
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

lemma slopeBall {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X→Y) (r A : ℝ) (he : ∀ x, ‖x‖<r → DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x‖ ≤ A) :
    ∀ x : X, ‖x‖ < r → ∀ y : X, ‖y‖ < r → ‖f x-f y‖ ≤ A*‖x-y‖ := by
  intro x hx y hy
  exact (convex_ball (0:X) r).norm_image_sub_le_of_norm_fderiv_le (f:=f) (𝕜:=ℝ)
    (fun v hv=> (he v ((dist_zero_right v) ▸ hv)).1) (fun v hv=> (he v ((dist_zero_right v) ▸ hv)).2)
    (Metric.mem_ball.mpr (by rwa [dist_zero_right])) (Metric.mem_ball.mpr (by rwa [dist_zero_right]))

namespace Warp
variable {G : Gauge} {c f : Side} (S : StepData c f) (H : Forest S.ratio)
open Green (address wt)
lemma testsRows {M : Matrix (Key H G) (Key H G) ℝ} {t C : ℝ}
    (h : ∀ (i : Key H G) (v : Key H G → ℝ), Amount t (address H) (address H i) v 1 → ‖(M*ᵥ v) i‖ ≤ C) :
    Green.Rows (address H) (address H) M t C := by
  intro i
  let w (j : Key H G) := wt t (address H i) (address H j)
  let v j := if 0 ≤ M i j then w j else -w j
  have he (j : Key H G) : 0 ≤ w j := (Green.wt_pos ..).le
  have he' : Amount t (address H) (address H i) v 1 := by
    intro j; unfold v
    rw [Green.wt_symm t _ (address H i),one_mul]; split
    · rw [Real.norm_of_nonneg (he j)]
    rw [norm_neg,Real.norm_of_nonneg (he j)]
  have hy : ∑ j,w j* |M i j|=(M*ᵥ v) i := by
    apply Finset.sum_congr rfl; intro j _; change w _ * _=_ * v j; unfold v; split
    · rename_i hi; rw [abs_of_nonneg hi,mul_comm]
    rename_i hi; rw [abs_of_neg (not_le.mp hi)]; ring
  exact hy.trans_le ((le_abs_self _).trans (h i v he'))
lemma both {M : Matrix (Key H G) (Key H G) ℝ} (h : M.IsHermitian) {t C : ℝ} (hh : Green.Rows (address H) (address H) M t C) :
    Green.Both (address H) (address H) M t C C := by
  have hv : M.transpose=M := by ext i j; simpa only [Matrix.transpose_apply,star_trivial] using (h.apply i j)
  exact ⟨hh,hv.symm ▸ hh⟩
def curvature (Q : Purchase) (G : Gauge) := Q.earnings 2*ColorCost G
lemma pays (Q : Purchase) (G : Gauge) : 1 ≤ curvature Q G := one_le_mul_of_one_le_of_one_le (Q.feesEarn 2) (color_ge G)
variable (p : Clip) (R : PathData G) (θ : S.Choices) {F : Site f→ChartVars H G→ℝ} {Q : Purchase} (hp : Q.Applies H p R F)
include hp

lemma inspection {x : ChartVars H G} (he : ‖x‖ < Q.width) {i : Key H G} {v : ChartVars H G} {c : ℝ} (hc : 0 ≤ c)
    (h : On S H G (Q.vacancy 2) (address H i) v c) : ‖fderiv ℝ (Analysis.D v (skew S H p R θ i)) x‖ ≤ Q.earnings 2*c := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (zero_le_one.trans (Q.feesEarn _)) hc) fun y => ?_
  let f := skew S H p R θ i
  let a : Fin 1→ChartVars H G := fun _=>y; let b := ‖y‖
  have he' := Q.pitch S H p R hp θ he i
  have ht : iteratedFDeriv ℝ 2 f x (Fin.cons v a)=D y (D v f) x := by rw [Analysis.cons_inner (j:=1) (he'.of_le le_top),iteratedFDeriv_one_apply]; rfl
  have hh := Q.accum S H p R hp θ he 2 i 2 le_rfl _ _ (menu_insert (d:=a) (c:=fun _=>b) (fun j=>⟨norm_nonneg y,Showroom.stamped S H _ (Q.vacant _).le y _⟩) h hc)
  unfold Polish.budget at hh; change ‖iteratedFDeriv ℝ 2 f x _‖ ≤ _ at hh
  rw [ht,Fin.prod_univ_succ, Fin.cons_zero] at hh
  exact hh.trans_eq (by rw [Fin.prod_univ_one]; unfold b; change Q.earnings 2 * (c*‖y‖)=_; ring)

lemma compare {x y : ChartVars H G} (he : ‖x‖ < Q.width) (hg : ‖y‖ < Q.width) :
    let t:=Q.vacancy 2; let C:=curvature Q G*‖x-y‖
    Green.Both (address H) (address H) (bend S H p R θ x - bend S H p R θ y) t C C := by
  intro t C
  refine both S H ((ambient S H p R θ hp he).sub (ambient S H p R θ hp hg)) (testsRows S H ?_)
  intro i v h
  let V := (code S H G).symm v; let T z := bend S H p R θ z
  have hv : code S H G V=v := ContinuousLinearEquiv.apply_symm_apply ..
  let b := ColorCost G; have hb : 0≤b := zero_le_one.trans (color_ge _)
  have hx := wallet S H (address H i) t V zero_le_one (hv.symm ▸ h); rw [mul_one] at hx
  let A : ChartVars H G := (0,V); have ha : On S H G t (address H i) A b := ⟨zeroed t _ _ G.Color hb,hx⟩
  rw [Matrix.sub_mulVec]; change ‖(T x*ᵥ v) i-(T y*ᵥ v) i‖ ≤ _; unfold T
  rw [← hv,← payout S H p R θ hp he,← payout S H p R θ hp hg]
  refine slopeBall (Analysis.D A (skew S H p R θ i)) _ _ (fun z hz => ⟨?_,inspection S H p R θ hp hz hb ha⟩) x he y hg
  exact (Analysis.dSmooth (Purchase.pitch S H p R hp θ hz i) _ (m:=ω) (by simp)).differentiableAt (by simp)

end Warp
end YM.AnalyticNext.QuarticMatch.Radius
