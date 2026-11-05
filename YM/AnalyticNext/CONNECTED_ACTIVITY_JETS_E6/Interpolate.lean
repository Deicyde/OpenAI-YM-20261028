import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brush
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Numerics

/-!
# Extrapolate geometric Color prices from FLAT

We will use *unscaled* polynomial jet bounds in gauge-local weak variables,
with cubic/quadratic orders unavailable unless one controls the remainders
of argument differentiation. Avoid high-order Taylor differentiation bounds
of the projected quadratic comparisons by probing **all** directions around the
flat patch (where they agree with unswitched formulas). Flat V not probed
for the final pushed/activity value; only for elementary jet accounting. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Metric Set
open scoped Topology BigOperators ContDiff Classical
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {d e u v : ℝ} {f : E→F}
private lemma velocity {x : E} (hd : 0 < d) (he : 0≤e) (hu : 0≤u)
    (h : ∀ y ∈ closedBall x d,DifferentiableAt ℝ f y ∧
      ‖fderiv ℝ f y-fderiv ℝ f x‖ ≤ e*d ∧ ‖f y‖≤u) :
    ‖fderiv ℝ f x‖ ≤ 2*u/d + e*d := by
  let F':=fderiv ℝ f x; let s:= closedBall x d
  have hx : x∈s := mem_closedBall_self hd.le
  have he' y (hy : y∈s) : ‖fderiv ℝ f y-F'‖ ≤ e*d := (h y hy).2.1
  apply ContinuousLinearMap.opNorm_le_bound' _ (by positivity)
  intro i hi
  let y := d*‖i‖⁻¹; let z := y • i+x
  have hv : 0<‖i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hi)
  have hp : 0<y := by unfold y; positivity
  have hb : z-x=y • i := add_sub_cancel_right _ _
  have hr : ‖z-x‖=d := by rw [hb,norm_smul, Real.norm_of_nonneg hp.le]; unfold y; field_simp
  have hz : z∈s := mem_closedBall_iff_norm.mpr hr.le
  have hf := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (fun i hi=> (h i hi).1.hasFDerivAt.hasFDerivWithinAt)
    he' (convex_closedBall x d) hx hz
  rw [hr,hb,map_smul] at hf
  have hg : y* ‖F' i‖ ≤ e*d*d+(u+u) := by
    rw [← Real.norm_of_nonneg hp.le,← norm_smul]
    have hh : F' (y • i)= y • F' i := map_smul ..
    have h' : -(f z-f x-y • F' i)+(f z-f x)=y • F' i := by abel
    calc
      _ = ‖-(f z-f x-y • F' i)+(f z-f x)‖ := by rw [h']
      _ ≤ _ := by apply (norm_add_le ..).trans; rw [norm_neg]; exact add_le_add hf ((norm_sub_le ..).trans (add_le_add (h z hz).2.2 (h x hx).2.2))
  refine le_of_mul_le_mul_left (hg.trans_eq ?_) hp
  unfold y; field_simp; ring

/-- Large radius B, small visibility test 3*b (parameter*hatTemp in use).
Recapture all Hessian costs even in directions of arbitrarily large `E`
DIMENSION (period-independent). -/

private lemma speeds {B : ℝ} (hu : 0≤u) (hd : 0<d) (hB : 3*d ≤ B) (hv : 0≤v)
    (p : ∀ i ∈ closedBall 0 B, ContDiffAt ℝ 3 f i ∧ normJ 3 f i ≤ v)
    (q : ∀ i∈ closedBall 0 (3*d), ‖f i‖≤u) :
    let w:=1000*(u/d^2+v*B)
    let y:=1000*u/d+w*B*3
    ∀ i∈ closedBall 0 B, normJ 2 f i ≤ w ∧ normJ 1 f i≤ y ∧ normJ 0 f i ≤ u+y*B := by
  intro w y
  let f' i:=iteratedFDeriv ℝ i f
  let s:= closedBall (0:E) B; let o := (0:E)
  have hp : 0 ≤ B := by linarith
  have hh (j : ℕ) (hj : j<3) i (hi : i ∈ s) : DifferentiableAt ℝ (f' j) i :=
    (p i hi).1.differentiableAt_iteratedFDeriv (by exact_mod_cast hj)
  have h0 : o∈s := mem_closedBall_self hp
  have h₃ : 3*d≥0 := by linarith
  let H := ‖f' 2 o‖
  have hlift (j : ℕ) i z : ‖fderiv ℝ (f' j) i-fderiv ℝ (f' j) z‖=‖f' (j+1) i - f' (j+1) z‖ := by
    unfold f'; rw [iteratedFDeriv_succ_eq_comp_left]; dsimp only [Function.comp_apply]
    rw [← dist_eq_norm, LinearIsometryEquiv.dist_map]; exact (dist_eq_norm (fderiv ℝ (f' j) i) (fderiv ℝ (f' j) z)).symm
  have hP (j : ℕ) i : ‖fderiv ℝ (f' j) i‖ = ‖f' (j+1) i‖ := norm_fderiv_iteratedFDeriv
  have h0' : 0 ≤ H := norm_nonneg _
  have hY z (hz : z∈s) i (hi : i∈s) : ‖f' 2 i-f' 2 z‖≤ v*‖i-z‖ := Convex.norm_image_sub_le_of_norm_fderiv_le
    (hh 2 (by norm_num)) (fun i hi=> (hP 2 i).trans_le (p i hi).2) (convex_closedBall o B) hz hi
  have hx i (hi : i∈s) : ‖f' 2 i‖ ≤ H + v*‖i‖ := by
    simpa only [H, o, sub_zero] using! ((norm_le_norm_add_norm_sub' (f' 2 i) (f' 2 o)).trans (add_le_add_right (hY _ h0 i hi) _))

  let p := closedBall (0:E) (2*d)
  have hU : 0<2*d := by positivity
  let r:= d/4
  have hr : 0<r := by unfold r; positivity
  let A := 2*u/r+(H+v*(3*d))*r
  have hA : 0 ≤ A := by unfold A; positivity
  have hD (i : E) (hi : i∈closedBall 0 (3*d)) := (closedBall_subset_closedBall hB) hi
  have hf i (hi : i∈p) : ‖f' 1 i‖ ≤ A := by
    rw [← hP 0]
    refine velocity hr (by positivity) hu ?_
    · intro j hj
      have he : j∈closedBall 0 (3*d) := by
        apply mem_closedBall.mpr; apply (dist_triangle j i 0).trans
        apply (add_le_add (mem_closedBall.mp hj) (mem_closedBall.mp hi)).trans
        unfold r; linarith
      have hJ y (hy : y∈closedBall i r) : y∈closedBall 0 (3*d) := by
        apply mem_closedBall.mpr; apply (dist_triangle y i 0).trans
        apply (add_le_add (mem_closedBall.mp hy) (mem_closedBall.mp hi)).trans; unfold r; linarith
      refine ⟨hh 0 (by norm_num) _ (hD _ he),?_,by unfold f'; rw [norm_iteratedFDeriv_zero]; exact q j he⟩
      rw [hlift]
      apply (Convex.norm_image_sub_le_of_norm_fderiv_le (f:=f' (0+1)) (fun y hy=> hh _ (by decide) y (hD _ (hJ _ hy)))
        (C:=H+v*(3*d)) ?_ (convex_closedBall i r) (mem_closedBall_self hr.le) hj).trans
      · exact mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hj) (by positivity)
      intro y hy
      refine (hP (0+1) _).trans_le ((hx y (hD _ (hJ y hy))).trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp (hJ _ hy)) hv) _))
  have hg : H ≤ 2*A/(2*d)+v*(2*d) := by
    unfold H; rw [← hP 1]
    have he i (hi : i∈p) := hD _ ((closedBall_subset_closedBall (show 2*d≤3*d by linarith)) hi)
    refine velocity hU hv hA fun i hi=> ⟨hh _ (by decide) i (he i hi),?_,hf _ hi⟩
    rw [hlift]; apply (hY _ h0 i (he _ hi)).trans
    exact mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hi) hv
  have hWide : H ≤ 50*(u/d^2+v*d) := by
    unfold A r at hg; field_simp at hg ⊢; nlinarith [show 0≤v*d^3 by positivity]

  have hw i (hi : i∈s) : ‖f' 2 i‖ ≤ w := by
    apply (hx i hi).trans
    have he : ‖i‖ ≤ B := mem_closedBall_zero_iff.mp hi
    unfold w
    have hv' := mul_le_mul_of_nonneg_left he hv; have hh : d ≤ B := by linarith
    linarith only [hv',hWide,mul_le_mul_of_nonneg_left hh hv,show 0 ≤ u/d^2+v*B by positivity,mul_nonneg hv hp,show 0≤u/d^2 by positivity]
  have hz : 0 ≤ w := (norm_nonneg _).trans (hw _ h0)
  have ht i (hi : i∈s) : ‖f' 1 i‖ ≤ y := by
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le (hh 1 (by decide)) (fun i hi=> (hP 1 i).trans_le (hw _ hi)) (convex_closedBall 0 B) h0 hi
    have hK := hf 0 (mem_closedBall_self hU.le)
    have h0x : (H+v*(3*d))*r ≤ w*B := by
      apply mul_le_mul _ _ hr.le hz
      · unfold w
        linarith only [hWide, mul_le_mul_of_nonneg_left hB hv,show 0≤v*d by positivity, show 0≤u/d^2 by positivity]
      unfold r; linarith
    have hI : ‖i-o‖≤B := mem_closedBall_iff_norm.mp hi
    have hE := mul_le_mul_of_nonneg_left hI hz
    have hb := norm_le_norm_add_norm_sub' (f' 1 i) (f' 1 o)
    have hr : 2*u/r=8*u/d := by unfold r; ring
    unfold A at hK; rw [hr] at hK; unfold y; unfold o at *
    apply (hb.trans (add_le_add hK (he.trans hE))).trans; simp only [mul_div_assoc]; linarith only [h0x, mul_nonneg hz hp,show 0 ≤ u/d by positivity]
  have hy : 0≤y := (norm_nonneg _).trans (ht o h0)
  intro i hi; constructor
  · exact hw _ hi
  refine ⟨ht _ hi,?_⟩
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le (hh 0 (by decide)) (fun i hi=> (hP 0 i).trans_le (ht _ hi)) (convex_closedBall o B) h0 hi
  exact (norm_le_norm_add_norm_sub' (f' 0 i) (f' 0 o)).trans (add_le_add
    ((norm_iteratedFDeriv_zero ..).trans_le (q 0 (mem_closedBall_self h₃))) (he.trans
    (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hi) hy)))

def paidHull (d B u v : ℝ) := let w:=1000*(u/d^2+v*B); let y:=1000*u/d+w*B*3
    u+(y*B+(y*d+(w*d^2+v*d^3)))
lemma ascend {k : ℕ} (hk : 3≤k) {B : ℝ} (hu : 0≤u) (hd : 0<d) (hh : d≤1) (hB : 3*d ≤ B)
    (hv : 0 ≤ v) (h : ∀ x,x∈closedBall (0:E) B→ Brush k v 1 f x)
    (p : ∀ x∈closedBall 0 (3*d), ‖f x‖≤u) (x : E) (hx : x∈closedBall 0 B) :
      Brush k (paidHull d B u v) d⁻¹ f x := by
  let w:=1000*(u/d^2+v*B); let y:=1000*u/d+w*B*3; let C:=paidHull d B u v
  have hb : 0≤B := by linarith
  have hw : 0≤w := by unfold w; positivity
  have hy : 0≤y := by unfold y; positivity
  have he (x : E) (hx : x∈ closedBall (0:E) B) := (Brush.offer.1 (h x hx)).2 3 hk
  obtain ⟨h1,h2,h3⟩:=speeds hu hd hB hv (fun x hx=> ⟨((h x hx).smaller hk).smooth, he x hx⟩) p x hx
  have ht : C=u+(y*B+(y*d+(w*d^2+v*d^3))) := rfl
  refine ⟨(h x hx).smooth,by positivity,fun i hi => ?_⟩
  rw [inv_pow,← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).2
  change _ ≤ C; rw [ht]
  rcases i with (_|_|_|i)
  · rw [pow_zero, mul_one]; change normJ 0 _ _ ≤ u+y*B at h3
    nlinarith only [h3,mul_nonneg hy hd.le,mul_nonneg hw (sq_nonneg d),show 0≤v*d^3 by positivity]
  · change normJ 1 _ _*d^1 ≤ _; rw [pow_one]
    change normJ 1 _ _≤y at h2; nlinarith only [mul_le_mul_of_nonneg_right h2 hd.le,mul_nonneg hy hb,
      mul_nonneg hw (sq_nonneg d),hu,show 0≤v*d^3 by positivity]
  · change normJ 2 _ _ * d^2 ≤ _; change normJ 2 _ _≤w at h1
    nlinarith only [mul_le_mul_of_nonneg_right h1 (sq_nonneg d),mul_nonneg hy hd.le,mul_nonneg hy hb,hu,show 0≤v*d^3 by positivity]
  apply le_trans (mul_le_mul ((Brush.offer.1 (h x hx)).2 _ hi) (pow_le_pow_of_le_one hd.le hh (Nat.le_add_left 3 i)) (pow_nonneg hd.le _) hv)
  nlinarith only [hu,mul_nonneg hy hd.le,mul_nonneg hw (sq_nonneg d),mul_nonneg hy hb]

open Lattice RG Pressure
variable {G : Gauge} {L : Side} {d' B u' v' : ℝ → ℝ} {a : ℝ}
lemma recover_price (h1 : Rate G L (-(1/2)) d') (h2 : Rate G L (-(1/2)) B) (h3 : Rate G L a u')
    (h4 : Rate G L 0 v') (ha : -(3/2:ℝ) ≤ a) (h5 : Rate G L (1/2) (fun x=> (d' x)⁻¹)) :
    Rate G L a (fun x=> paidHull (d' x) (B x) (u' x) (v' x)) := by
  have hw : Rate G L (a+1) (fun x=>1000*(u' x/(d' x)^2+v' x*B x)) := by
    apply Rate.mul_left
      (w:=fun x=> u' x/(d' x)^2+v' x*B x) (Rate.add ?_ ((h4.mul h2).weaken (by linarith)))
    have hv:= h3.mul (h5.pow 2)
    simp only [inv_pow,← div_eq_mul_inv] at hv; convert hv using 1; push_cast; ring
  have hy:= (hw.mul h2).mul_right 3
  dsimp only [paidHull]
  simp_rw [div_eq_mul_inv (1000 * u' _)]
  have hx:= (h3.mul_left 1000).mul h5
  have he := hx.add (hy.weaken (by linarith))
  apply h3.add
  apply Rate.add ((he.mul h2).weaken (by linarith))
  apply Rate.add ((he.mul h1).weaken (by linarith))
  exact ((hw.mul (h1.pow 2)).weaken (by push_cast; linarith)).add ((h4.mul (h1.pow 3)).weaken (by push_cast; linarith))
end YM.ConnectedActivityE6.Blaze
