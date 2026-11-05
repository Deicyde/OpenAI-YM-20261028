import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment

/-! # Resume quantitative parameter smoothing. Specific widths and flat
 subtraction order sufficient, not polynomial guess from field values.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lantern
open Push.AbsoluteSums Lattice RG Pressure Function Filter Set Metric MeasureTheory
open ConnectedActivityE6 Blaze Brush
open scoped Topology ContDiff BigOperators Classical
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {u : E→F} {x : E} {C d e ε v r A B K : ℝ} {j n : ℕ}
-- from Blaze.Interpolate proof
lemma velocity {u : ℝ} {f : E→F} {x : E} (hd : 0 < d) (he : 0≤e) (hu : 0≤u)
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

lemma up_one (hd : 0<d) (hv : 0≤v) (hc : 0 ≤ C) (H : ∀ y∈closedBall x d, Brush (j+2) C 1 u y) (hr : ∀ y∈closedBall x d, normJ j u y ≤ v) : normJ (j+1) u x ≤ 2*v/d+C*d := by
  let f:=iteratedFDeriv ℝ j u; let h:=iteratedFDeriv ℝ (j+1) u
  have hg y : fderiv ℝ f y=continuousMultilinearCurryLeftEquiv ℝ (fun _=>E) F (h y) := congr_fun fderiv_iteratedFDeriv y
  unfold normJ; rw [← norm_fderiv_iteratedFDeriv]; apply velocity hd hc hv
  intro y hy; refine ⟨(H y hy).smooth.differentiableAt_iteratedFDeriv (by exact_mod_cast (show j<j+2 by omega)), ?_,hr y hy⟩
  have he := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=h)
    (fun i hi=> (H _ hi).smooth.differentiableAt_iteratedFDeriv (by exact_mod_cast (show j+1 < j+2 by omega)))
    (fun i hi=> norm_fderiv_iteratedFDeriv.trans_le ((Brush.offer.1 (H i hi)).inside _ le_rfl)) (mem_closedBall_self hd.le) hy
  rw [hg,hg, ← dist_eq_norm,LinearIsometryEquiv.dist_map,dist_eq_norm]
  exact he.trans (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hy) hc)
lemma iteration (G : Gauge) (L : Side) (j : ℕ) {m a d : ℝ} (ha : 0<a) : -- hide widths p on stage
    ∃ B:ℝ, ∀ᶠ x in atTop, let z:=Pressure.betaF G x L
      ∀ (E F:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
        (u:E→F) (y:E), (∀ x ∈ closedBall y (z^(-a)), Brush (j+1) (z^d) 1 u x) → (∀ x∈ closedBall y (z^(-a)), ‖u x‖≤ z^B) → Brush j (z^m) 1 u y := by
  induction j generalizing m a with
  | zero=>
    refine ⟨m,?_⟩; filter_upwards [Delay.shift_pos G L] with x hx z E F _ _ _ _ u y hv he
    have hx : 0<z:=hx; have ht:y∈ closedBall y (z^(-a)):= mem_closedBall_self (by positivity)
    apply Brush.offer.2; refine ⟨((hv y ht).smaller (by decide)).smooth,?_⟩; intro i hi
    rw [show i=0 by omega]; exact (norm_iteratedFDeriv_zero ..).trans_le (he _ ht)
  | succ i ih=>
    let c : ℝ := a+max 0 (d-m)+1
    have hh:a < c:= by unfold c; linarith [le_max_left 0 (d-m)]
    let b:= m-1-c
    obtain ⟨B,hB⟩:= ih (m:=b) (ha.trans hh)
    have hr:= Rate.power (G:=G) (L:=L)
      (a:=-c)
    have hu := (hr.mul_left 2) (-a) (by linarith)
    have hz:= Rate.power (G:=G) (L:=L) (a:=b)
    have he:= (((hz.mul_left 2).mul (Rate.power (G:=G) (L:=L) (a:=c))).weaken (show b+c ≤ max (b+c) (d+-c) from le_max_left ..)).add (((Rate.power (G:=G) (L:=L) (a:=d)).mul hr).weaken (le_max_right ..))
    have he := he m (by apply max_lt; unfold b; linarith only; unfold c; linarith only [ha,le_max_right 0 (d-m)])
    refine ⟨B,?_⟩; filter_upwards [hB,hu, he,(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hH hr' he hx z E F _ _ _ _ f y hd hK
    have hv : 1 ≤ z := hx; have hx:0<z:=zero_lt_one.trans_le hv
    let s:=z^(-c); let t:=z^(-a); have hs:0<s:=by positivity
    have h2:2*s≤t:= (le_abs_self _).trans hr'
    have hh u (hu : u∈closedBall y s) : closedBall u s⊆ closedBall y t := fun v hv=> mem_closedBall.mpr
      (((dist_triangle v u y).trans (add_le_add (mem_closedBall.mp hv) (mem_closedBall.mp hu))).trans ((two_mul s) ▸ h2))
    have ht : closedBall y s ⊆ closedBall y t:= hh y (mem_closedBall_self hs.le)
    have hQ u (hu : u∈closedBall y s) : Brush i (z^b) 1 f u := hH E F f u
      (fun x hx=> (hd x (hh u hu hx)).smaller (by omega)) (fun x hx=> hK x (hh u hu hx))
    have h0:y∈closedBall y s:=mem_closedBall_self hs.le
    apply Brush.offer.2; refine ⟨((hd _ (ht h0)).smaller (Nat.le_succ _)).smooth, fun j hj=> ?_⟩
    rcases eq_or_lt_of_le hj with h|h
    · subst j; refine (up_one hs (by positivity) (by positivity) (fun i hi=>hd i (ht hi)) (fun j hj=> (Brush.offer.1 (hQ _ hj)).2 _ le_rfl)).trans ?_
      unfold s; rw [div_eq_mul_inv,Real.rpow_neg hx.le] -- goal occurrences simplify abs mismatch
      apply le_trans _ ((le_abs_self _).trans he)
      rw [show Pressure.betaF G x L ^ (-c)= _ from Real.rpow_neg hx.le c, inv_inv]
    exact ((Brush.offer.1 (hQ y h0)).2 j (by omega)).trans (Real.rpow_le_rpow_of_exponent_le hv (by unfold b; linarith))
end YM.PhysicalNext.Repeat.Lantern
