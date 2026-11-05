import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment

/-!
# Even b estimate for truncated bulk Laplace correction. In full x order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lantern
open Function Filter Set Metric MeasureTheory ContinuousMultilinearMap
open ConnectedActivityE6 Blaze Brush
open scoped Topology ContDiff BigOperators Classical
variable {E F Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {j n : ℕ}
lemma shift_affine (x : E) (a : F) (P : E→L[ℝ] F) {f : F→Y} (k : ℕ) (h : ContDiffAt ℝ (↑ k) f (a+P x)) :
    iteratedFDeriv ℝ k (fun y=> f (a+P y)) x = (iteratedFDeriv ℝ k f (a+P x)).compContinuousLinearMap (fun _ => P) := by
  let g y:= f (a+y)
  change iteratedFDeriv ℝ k (g ∘ P) x=_
  rw [WardBin.Lies.liner P (show ContDiffAt ℝ (↑k) g (P x) from h.comp (f:=fun t : F=>a+t) _ (contDiffAt_const.add contDiffAt_id)),
    (show iteratedFDeriv ℝ k g (P x) = _ from iteratedFDeriv_comp_add_left ..)]
lemma skim {d e : ℝ} (x : E) {y : F} {P : E→L[ℝ] F} {f : F→Y} {k : ℕ} (h : Brush k d e f (y+P x)) (hp : ‖P‖ ≤ 1) : Brush k d e (fun v=> f (y+P v)) x := by
  refine ⟨h.smooth.comp (f:=fun v=>y+P v) _ (contDiffAt_const.add P.contDiff.contDiffAt),h.pos,fun i hi=>?_⟩
  unfold normJ; rw [shift_affine _ _ _ _ (h.smaller hi).smooth]; refine (norm_compContinuousLinearMap_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ?_).trans (h.order _ hi)); simp only [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) hp

section x
variable (u : ℝ×E→F) (j : ℕ)
abbrev arc {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (t : ℝ) (x : A) := (t,x)
abbrev hook (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] := ContinuousLinearMap.inr ℝ ℝ E
lemma n_hook : ‖hook E‖≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> by simp
lemma receipt (t : ℝ) (x : E) (h : ContDiffAt ℝ (↑ j) u (t,x)) :
    iteratedFDeriv ℝ j (u ∘ arc t) x=compContinuousLinearMapL (fun _ : Fin j=> hook E) (iteratedFDeriv ℝ j u (t,x)) := by
  have hx y: arc t y=(t,0)+(hook E y) := by simp
  have he := shift_affine (f:=u) x (t,0) (hook E) j ((hx x) ▸ h)
  rw [show u ∘ arc t=_ from funext fun y=> congr_arg u (hx y),he,← hx]; rfl

lemma eParity (v:ℝ→Y) {d C:ℝ} (hf : 0 < d) (H : ∀ t, ‖t‖ ≤ d → DifferentiableAt ℝ v t)
    (hp : (v ∘ fun x=> -x)=ᶠ[𝓝 (0:ℝ)] v) (h : ∀ t,‖t‖≤d → ‖fderiv ℝ v t-fderiv ℝ v 0‖≤ C*d) : ‖v d-v 0‖ ≤ C*d*d := by
  let N:= -ContinuousLinearMap.id ℝ ℝ
  have hu:(v ∘ N)=ᶠ[𝓝 0] v:=hp
  have hF : DifferentiableAt ℝ v (N 0):= by rw [_root_.map_zero]; exact H 0 (by simpa using hf.le)
  have hx : fderiv ℝ v 0=0:= by
    let t:= fderiv ℝ v 0; have he:fderiv ℝ (v ∘ N) 0=fderiv ℝ v 0:=hu.fderiv_eq; rw [fderiv_comp _ hF N.differentiableAt,N.fderiv,_root_.map_zero] at he
    apply ContinuousLinearMap.ext; intro x; have hp := congr_arg (fun P : ℝ→L[ℝ] Y=> P x) he
    simp only [ContinuousLinearMap.comp_apply,N,_root_.neg_apply,ContinuousLinearMap.id_apply,map_neg] at hp
    have hg : (2:ℝ) • t x=0:= by rw [show (2:ℝ)=1+1 by ring,add_smul,one_smul]; change -(t x)=t x at hp; nth_rw 1 [← hp]; rw [neg_add_cancel]
    exact (smul_eq_zero.mp hg).resolve_left (by norm_num)
  have hh := (convex_closedBall (0:ℝ) d).norm_image_sub_le_of_norm_fderiv_le (f:=v) (fun i hi=> H i (mem_closedBall_zero_iff.mp hi))
    (fun i hi=> (show ‖fderiv ℝ v i‖ ≤ _ from by simpa only [hx, sub_zero] using h i (mem_closedBall_zero_iff.mp hi))) (mem_closedBall_self hf.le) (show d∈closedBall 0 d by simp [abs_of_pos hf])
  simpa only [sub_zero,Real.norm_of_nonneg hf.le] using hh

lemma shoots (x : E) (v : ℝ) {C : ℝ} (hv : 0<v) (ht : u ∘ (fun x:ℝ×E=>(-x.1,x.2))=u)
    (h : ∀ t, ‖t‖ ≤ v → Brush (j+2) C 1 u (t,x)) : Brush j (C*v*v) 1 (u ∘ arc v - u ∘ arc 0) x := by
  have hm t (he : ‖t‖ ≤ v) : ContDiffAt ℝ (↑j) (u ∘ arc t) x := ((h t he).smaller (Nat.le_add_right j 2)).smooth.comp (f:=arc t) x (contDiffAt_const.prodMk contDiffAt_id)
  have hv₁ : ‖v‖ ≤ v := by rw [Real.norm_of_nonneg hv.le]
  have h₀:‖(0:ℝ)‖≤v:= by simpa using hv.le
  apply Brush.offer.2; refine ⟨(hm v hv₁).sub (hm 0 h₀),fun i hi=>?_⟩
  let L : ((ℝ×E) [×i]→L[ℝ] F) →L[ℝ] (E [×i]→L[ℝ] F):= compContinuousLinearMapL (fun _=>hook E)
  let k : ℝ×E→_ := iteratedFDeriv ℝ i u; let X (v:ℝ):=(v,x)
  let f:= L ∘ k ∘ X
  have hf t (he:‖t‖ ≤ v): f t=iteratedFDeriv ℝ i (u ∘ arc t) x := (receipt u i t x ((h _ he).smaller (by omega)).smooth).symm
  have hr t (he:‖t‖ ≤ v) : DifferentiableAt ℝ k (X t) := (h _ he).smooth.differentiableAt_iteratedFDeriv (by exact_mod_cast (show i<j+2 by omega))
  let P:= ContinuousLinearMap.inl ℝ ℝ E
  have hx : ∀ t,HasFDerivAt X P t := fun t=> (hasFDerivAt_id _).prodMk (hasFDerivAt_const ..) -- maybe id'
  have hd t (he:‖t‖ ≤ v) : DifferentiableAt ℝ f t := L.differentiableAt.comp _ ((hr t he).comp _ (hx t).differentiableAt)
  unfold normJ; rw [iteratedFDeriv_sub_apply ((hm v hv₁).of_le (Nat.cast_le.mpr hi)) ((hm 0 h₀).of_le (Nat.cast_le.mpr hi)),← hf v hv₁,← hf 0 h₀]
  apply eParity f hv hd
  · filter_upwards [Metric.ball_mem_nhds 0 hv] with t ht'
    have he : ‖t‖ ≤ v := (mem_ball_zero_iff.mp ht').le
    rw [Function.comp_apply,hf t he,hf (-t) (by simpa)]
    exact congr_arg (fun f => iteratedFDeriv ℝ i f x) (funext fun y=> congr_fun ht (t,y))
  intro t he; have hp : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> by simp [P]
  have hK : ‖L‖ ≤ 1 := (norm_compContinuousLinearMapL_le F (fun _ : Fin i=>hook E)).trans (by simp only [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) n_hook)
  have hF t (he:‖t‖≤v) : fderiv ℝ f t=L.comp ((fderiv ℝ k (X t)).comp P) := (L.hasFDerivAt.comp t ((hr t he).hasFDerivAt.comp t (hx t))).fderiv
  let g := iteratedFDeriv ℝ (i+1) u
  have hy a (ha : a∈closedBall (0:ℝ) v) : DifferentiableAt ℝ g (X a) := (h _ (mem_closedBall_zero_iff.mp ha)).smooth.differentiableAt_iteratedFDeriv (by exact_mod_cast (show i+1 < j+2 by omega))
  have hδ a (ha : a∈closedBall (0:ℝ) v) : ‖fderiv ℝ (g ∘ X) a‖ ≤ C := by
    rw [fderiv_comp a (hy _ ha) (hx _).differentiableAt,(hx _).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) hp).trans ?_)
    rw [show ‖fderiv ℝ g (X a)‖=_ from norm_fderiv_iteratedFDeriv]; exact (Brush.offer.1 (h a (mem_closedBall_zero_iff.mp ha))).inside _ (by omega)
  have hκ := (convex_closedBall (0:ℝ) v).norm_image_sub_le_of_norm_fderiv_le (fun a ha=> (hy _ ha).comp _ (hx _).differentiableAt) hδ (mem_closedBall_self hv.le) (mem_closedBall_zero_iff.mpr he)
  have heq : L.comp ((fderiv ℝ k (X t)).comp P)-L.comp ((fderiv ℝ k (X 0)).comp P)=L.comp ((fderiv ℝ k (X t)-fderiv ℝ k (X 0)).comp P):= by ext; simp
  rw [hF t he,hF 0 h₀,heq]
  refine (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hK).trans ((ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) hp).trans ?_)))
  have hz : ‖fderiv ℝ k (X t)-fderiv ℝ k (X 0)‖=‖g (X t)-g (X 0)‖:= by symm; unfold g; rw [iteratedFDeriv_succ_eq_comp_left]; dsimp only [comp_apply]; rw [← dist_eq_norm,LinearIsometryEquiv.dist_map]; exact dist_eq_norm ..
  rw [hz]; apply hκ.trans (mul_le_mul_of_nonneg_left (by simpa using he) (h 0 h₀).nonneg)
end x
end YM.PhysicalNext.Repeat.Lantern
