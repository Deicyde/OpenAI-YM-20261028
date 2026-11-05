import YM.Push.LOOP_COEFFICIENT.Pullback

/-! # Separating field slots and higher derivatives on exponential germs -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Function Filter Set Matrix
open scoped Topology ContDiff BigOperators
variable {E F H 𝕜 : Type} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup H]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 H]
  {r s : ℕ} {x : E} {f : E → F}

/-- Append without awkward proof casts under left recursion. -/
def prepend {E : Type} {r} (v : Fin r → E) : {s : ℕ} → (Fin s → E) → Fin (r+s) → E
  | 0,_ => v
  | _+1,u => Fin.cons (u 0) (prepend v (Fin.tail u))

lemma action_smooth (h : ContDiffAt 𝕜 ω f x) (v : Fin r → E) : ContDiffAt 𝕜 ω (fun x => iteratedFDeriv 𝕜 r f x v) x :=
  (ContinuousMultilinearMap.apply 𝕜 (fun _ => E) F v).contDiff.contDiffAt.comp x (h.iteratedFDeriv_right (by simp))
lemma iterated_at (h : ContDiffAt 𝕜 ω f x) (v : Fin r → E) (w : E) :
    fderiv 𝕜 (fun x => iteratedFDeriv 𝕜 r f x v) x w = iteratedFDeriv 𝕜 (r+1) f x (Fin.cons w v) := by
  let L := ContinuousMultilinearMap.apply 𝕜 (fun _ => E) F v
  have he := (h.iteratedFDeriv_right (m:=ω) (i:=r) (by simp)).differentiableAt (by simp)
  change fderiv 𝕜 (L ∘ _) _ _ = _
  rw [fderiv_comp _ L.differentiableAt he,L.fderiv,iteratedFDeriv_succ_apply_left]; simp only [Fin.cons_zero, Fin.tail_cons]; rfl

lemma split_iterated (h : ContDiffAt 𝕜 ω f x) (v : Fin r → E) (w : Fin s → E) : iteratedFDeriv 𝕜 s (fun x => iteratedFDeriv 𝕜 r f x v) x w =
    iteratedFDeriv 𝕜 (r+s) f x (prepend v w) := by
  induction s generalizing x with
  | zero => rw [iteratedFDeriv_zero_apply]; rfl
  | succ s ih =>
    have he := action_smooth h v
    have hh : (fun x => iteratedFDeriv 𝕜 s (fun x => iteratedFDeriv 𝕜 r f x v) x (Fin.tail w)) =ᶠ[𝓝 x] (fun x => iteratedFDeriv 𝕜 (r+s) f x (prepend v (Fin.tail w))) := (h.eventually (by simp)).mono fun y hy => ih hy _
    rw [← Fin.cons_self_tail w, ← iterated_at he,Fin.cons_self_tail, prepend, hh.fderiv_eq,iterated_at h]; rfl

lemma iterated_affine (L : H →L[𝕜] E) (z : E) (y : H) (h : ContDiffAt 𝕜 ω f (z+L y)) (v : Fin r → H) :
    iteratedFDeriv 𝕜 r (fun y => f (z+L y)) y v = iteratedFDeriv 𝕜 r f (z+L y) (fun i => L (v i)) := by
  induction r generalizing y with
  | zero => simp
  | succ n ih =>
    let g y := z+L y
    have hg : ContDiff 𝕜 ω g := contDiff_const.add L.contDiff
    have eq : (fun x => iteratedFDeriv 𝕜 n (fun y => f (g y)) x (Fin.tail v)) =ᶠ[𝓝 y] fun x => iteratedFDeriv 𝕜 n f (g x) (fun i => L (v i.succ)) := ((hg.continuous.tendsto y).eventually (h.eventually (by simp))).mono fun x hx => ih x hx _
    rw [← Fin.cons_self_tail v,← iterated_at (show ContDiffAt 𝕜 ω (fun y => f (z+L y)) y from h.comp (f:=g) y hg.contDiffAt), Fin.cons_self_tail, ← Fin.cons_self_tail (fun i => L (v i)), ← iterated_at h]
    change fderiv 𝕜 (fun x => iteratedFDeriv 𝕜 n (fun y => f (g y)) x (Fin.tail v)) y _ = _; rw [eq.fderiv_eq]
    rw [show fderiv 𝕜 (fun x => iteratedFDeriv 𝕜 n f (g x) (fun i => L (v i.succ))) y = _ from fderiv_comp (g:=fun x => iteratedFDeriv 𝕜 n f x fun i => L (v i.succ)) y ((action_smooth h _).differentiableAt (by simp)) (hg.differentiable (by simp) y), ContinuousLinearMap.comp_apply,show fderiv 𝕜 g y = _ from (fderiv_const_add _).trans L.fderiv]; rfl

lemma mixed_partial (A B : H →L[𝕜] E) (h : ContDiffAt 𝕜 ω f 0) (v : Fin r → H) (w : Fin s → H) :
    iteratedFDeriv 𝕜 s (fun b => iteratedFDeriv 𝕜 r (fun a => f (B b + A a)) 0 v) 0 w = iteratedFDeriv 𝕜 (r+s) f 0 (prepend (fun i => A (v i)) fun i => B (w i)) := by
  have eq : (fun b => iteratedFDeriv 𝕜 r (fun a => f (B b + A a)) 0 v) =ᶠ[𝓝 (0:H)] (fun b => iteratedFDeriv 𝕜 r f (0+B b) fun i => A (v i)) := ((B.continuous.tendsto 0).eventually (B.map_zero.symm ▸ h.eventually (by simp))).mono fun b hb => by simpa only [zero_add,map_zero,add_zero] using iterated_affine A (B b) 0 (show ContDiffAt 𝕜 ω f (B b + A 0) by simpa using hb) v
  rw [(eq.iteratedFDeriv 𝕜 s).self_of_nhds, iterated_affine (f:=fun z => iteratedFDeriv 𝕜 r f z (fun i => A (v i))) B 0 0 (by rw [map_zero,add_zero]; exact action_smooth h _),map_zero,add_zero, split_iterated h]
lemma mixed_smooth (A B : H →L[𝕜] E) (h : ContDiffAt 𝕜 ω f 0) (v : Fin r → H) : ContDiffAt 𝕜 ω (fun b => iteratedFDeriv 𝕜 r (fun a => f (B b + A a)) 0 v) 0 := by
  have he := (action_smooth h fun i => A (v i))
  rw [← B.map_zero] at he
  exact (he.comp (f:=B) 0 B.contDiff.contDiffAt).congr_of_eventuallyEq (((B.continuous.tendsto 0).eventually (B.map_zero.symm ▸ h.eventually (by simp))).mono fun b hb => by simpa only [Function.comp_apply,map_zero,add_zero] using iterated_affine A (B b) 0 (show ContDiffAt 𝕜 ω f (B b + A 0) by simpa using hb) v)

variable [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {g : A → B}

lemma real_slots (P : A →L[ℝ] E) (Q : B →L[ℝ] F) (h : ContDiffAt ℂ ω f 0) (hg : ContDiffAt ℝ ω g 0) (hf : (Q ∘ g) =ᶠ[𝓝 0] f ∘ P) (v : Fin r → A) :
    Q (iteratedFDeriv ℝ r g 0 v) = iteratedFDeriv ℂ r f 0 (fun i => P (v i)) := by
  rw [show Q (iteratedFDeriv ℝ r g 0 v) = iteratedFDeriv ℝ r (Q ∘ g) 0 v from ?_,(hf.iteratedFDeriv ℝ r).self_of_nhds,
    show f ∘ P = (fun z => f (0+P z)) from funext fun z => (congr_arg f (zero_add _)).symm,
    iterated_affine P 0 0 (show ContDiffAt ℝ ω f _ by simpa using h.restrict_scalars ℝ),map_zero,add_zero,
    ← (h.of_le (m:=(r:WithTop ℕ∞)) le_top).restrictScalars_iteratedFDeriv]; rfl
  rw [Q.iteratedFDeriv_comp_left hg le_top]; rfl
end YM.Push.Loops.Paths
