import YM.Extra.FREE_DETECTOR_ALGEBRA.Translation

set_option warningAsError false

/-! Tools to perform radial/angular extractions of the Ward tests.
Polynomial here on *positions* in E4. No extension through collisions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.SphereTest
open Function Filter Set Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {F M N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup N] [NormedSpace ℝ N]
variable {f g : E4 → F} {h : E4 → M} {j k : ℕ}

structure Pure (k : ℕ) (f : E4 → F) : Prop where
  smooth : ContDiff ℝ ∞ f
  rad (x : E4) (t : ℝ) : f (t • x) = t^k • f x

lemma Pure.plus (hf : Pure j f) (hg : Pure j g) : Pure j (f+g) :=
    ⟨hf.smooth.add hg.smooth, fun x t => by simp [hf.rad,hg.rad,smul_add]⟩
lemma Pure.minus (hf : Pure j f) (hg : Pure j g) : Pure j (f-g) :=
    ⟨hf.smooth.sub hg.smooth, fun x t => by simp [hf.rad,hg.rad,smul_sub]⟩
lemma Pure.vScale (hf : Pure j f) (t : ℝ) : Pure j (t • f) :=
    ⟨contDiff_const.smul hf.smooth, fun x y => by simp [hf.rad,smul_comm t]⟩
lemma Pure.linear (hf : Pure j f) (L : F→L[ℝ] M) : Pure j (fun x => L (f x)) :=
    ⟨L.contDiff.comp hf.smooth,fun x t => by rw [hf.rad,map_smul]⟩
lemma Pure.bilinear (hf : Pure j f) (hg : Pure k h) (L : F →L[ℝ] M →L[ℝ] N) : Pure (j+k) (fun x => L (f x) (h x)) :=
    ⟨(L.contDiff.comp hf.smooth).clm_apply hg.smooth, fun x t => by rw [hf.rad,hg.rad,map_smul L,smul_apply,map_smul,pow_add,mul_smul]⟩
lemma Pure.sumf {ι : Type*} (s : Finset ι) (f : ι→E4→F) (h : ∀ i∈s,Pure j (f i)) : Pure j (fun x => ∑ i ∈ s, f i x) :=
    ⟨ContDiff.sum (fun i hi => (h i hi).smooth),fun x t => (Finset.sum_congr rfl (fun i hi => (h i hi).rad x t)).trans (Finset.smul_sum ..).symm⟩
lemma pure_zero (j : ℕ) : Pure j (fun _ => (0:F)) := ⟨contDiff_const,fun _ _ => (smul_zero ..).symm⟩
lemma pure_diag (P : T E4 F j) : Pure j (diagonal P) := ⟨diag_smooth _ _, homogeneous _⟩

lemma Pure.tensor (hf : Pure j f) : ∃ P : T E4 F j, f = diagonal P ∧ Sym P := by
  have ht : ContDiffAt ℝ j f 0 := hf.smooth.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨coeff f _ 0, funext fun i => ?_, coeff_symm ht⟩
  rw [along ht]; simp_rw [zero_add,hf.rad]; rw [deriv_power (f:=fun t : ℝ => f i) contDiffAt_const (show j≤j from le_rfl)]
  rw [if_pos rfl,smul_smul,inv_mul_cancel₀ (by positivity),one_smul]

lemma Pure.euler (hf : Pure j f) (x : E4) : ∑ i : Axis, x i • grad i f x = (j:ℝ) • f x := by
  obtain ⟨A,rfl,hA⟩ := hf.tensor; exact grad_euler A hA x

lemma Pure.zeroth {f : E4 → F} (hf : Pure 0 f) : f = fun _ => f 0 := funext fun x => by
  have hi := hf.rad x 0; simpa using hi.symm

lemma Pure.derive (hf : Pure (j+1) f) (a : Axis) : Pure j (grad a f) := by
  obtain ⟨A,rfl,hA⟩ := hf.tensor
  rw [show grad a (diagonal A) = ((j+1:ℕ):ℝ) • diagonal (A.curryLeft (basis a)) by
    funext i; unfold grad D; rw [differential_diagonal A hA i (basis a)]; simp only [Pi.smul_apply,Nat.cast_smul_eq_nsmul]; rfl]
  exact (pure_diag _).vScale _

lemma Pure.laplace (hf : Pure (j+2) f) : Pure j (lap f) := Pure.sumf _ _ fun i _ => (hf.derive i).derive i

section calculus
lemma grad_diff_all (hf : ContDiff ℝ ∞ f) (i) : ContDiff ℝ ∞ (grad i f) := by
  rw [contDiff_iff_contDiffAt]; exact fun x => grad_smooth_at hf.contDiffAt i

lemma lap_zero (c : F) : lap (fun _ => c) = fun _ => 0 := by
  ext1 x; unfold lap
  have ht (a) : grad a (fun _ => c) = fun _ => 0 := by funext x; simp [grad,D]
  simp_rw [ht]; simp [grad,D]



lemma lap_scale' (hf : ContDiff ℝ ∞ f) (a : ℝ) : lap (a • f)=a • lap f := by
  funext x; unfold lap
  have he i : grad i (a • f)= a • grad i f := funext fun y => grad_smul hf.contDiffAt i a
  simp_rw [he,fun i => grad_smul (grad_diff_all hf i).contDiffAt (x:=x) i a, ← Finset.smul_sum]; rfl

lemma lap_add' (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : lap (f+g)=lap f+lap g := by
  funext x; unfold lap
  have he i : grad i (f+g)=grad i f+grad i g := funext fun _ => grad_plus hf.contDiffAt hg.contDiffAt i
  simp_rw [he,fun i => grad_plus (grad_diff_all hf i).contDiffAt (grad_diff_all hg i).contDiffAt (x:=x) i, Finset.sum_add_distrib]; rfl

lemma lap_sub' (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : lap (f-g)=lap f-lap g := by
  rw [sub_eq_add_neg,show -g=(-1:ℝ) • g by simp, lap_add' hf (show ContDiff ℝ ∞ ((-1:ℝ) • g) from by simp; exact hg.neg),lap_scale' hg]; simp [sub_eq_add_neg]

lemma lap_linear (hf : ContDiff ℝ ∞ f) (L : F→L[ℝ] M) : lap (fun x => L (f x)) = fun x => L (lap f x) := by
  have ht (i) (f : E4 → F) (hf : ContDiff ℝ ∞ f) : grad i (fun y => L (f y)) = fun y => L (grad i f y) :=
    funext fun y => grad_linear L hf.contDiffAt _
  funext x; unfold lap; simp_rw [fun i => ht i f hf, fun i => ht i _ (grad_diff_all hf i), map_sum]


lemma grad_pair (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ h) (B : F →L[ℝ] M →L[ℝ] N) (i : Axis) :
    grad i (fun x => B (f x) (h x)) = (fun x => B (f x) (grad i h x)) + (fun x => B (grad i f x) (h x)) := by
  funext x
  have hu := (B.contDiff.comp hf).differentiable (by simp) x
  change fderiv ℝ (fun y => (B ∘ f) y (h y)) x _ = _
  rw [fderiv_clm_apply hu (hg.differentiable (by simp) x), fderiv_comp x B.differentiableAt (hf.differentiable (by simp) x), B.fderiv]
  rfl

lemma lap_pair (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ h) (B : F →L[ℝ] M →L[ℝ] N) (x : E4) :
    lap (fun x => B (f x) (h x)) x = B (lap f x) (h x) + B (f x) (lap h x) +
      (2:ℝ) • ∑ a : Axis, B (grad a f x) (grad a h x) := by
  unfold lap
  have he (a : Axis) : grad a (grad a (fun x => B (f x) (h x))) x =
      B (grad a (grad a f) x) (h x) + B (f x) (grad a (grad a h) x) + (2:ℝ) • B (grad a f x) (grad a h x) := by
    have hp := grad_diff_all hf a; have hh := grad_diff_all hg a
    rw [grad_pair hf hg B a, grad_plus
      (show ContDiffAt ℝ ∞ (fun x => B (f x) (grad a h x)) x from ((B.contDiff.comp hf).clm_apply hh).contDiffAt) (show ContDiffAt ℝ ∞ (fun x => B (grad a f x) (h x)) x from ((B.contDiff.comp hp).clm_apply hg).contDiffAt),
      grad_pair hf hh B a,grad_pair hp hg B a,two_smul]
    simp only [Pi.add_apply]; abel
  simp_rw [he,Finset.sum_add_distrib,← Finset.smul_sum,map_sum,sum_apply]

def coordF (i : Axis) (x : E4) : ℝ := x i

def qRad (x : E4) := ‖x‖^2

lemma pure_coordF (i : Axis) : Pure 1 (coordF i) := ⟨(compAxis i).contDiff,fun x t => by rw [pow_one]; rfl⟩
lemma pure_square : Pure 2 qRad := ⟨contDiff_norm_sq ℝ,fun x t => by simp [qRad,norm_smul,mul_pow]⟩

lemma grad_coordF (a b : Axis) : grad a (coordF b) = fun _ => if a=b then 1 else 0 := by
  funext x
  change fderiv ℝ (compAxis b) x (basis a) = _
  rw [(compAxis b).fderiv]; change basis a b = _; simp [eq_comm]

lemma lap_coordF (a : Axis) : lap (coordF a) = 0 := by
  funext x; unfold lap; simp_rw [grad_coordF]; simp [grad,D]

lemma grad_square (a : Axis) : grad a qRad = (2:ℝ) • coordF a := by
  funext x; unfold grad D qRad
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp [two_smul,← real_inner_comm x,coordF]; ring

lemma lap_square : lap qRad = fun _ => 8 := by
  funext x; unfold lap
  simp_rw [grad_square,fun a => grad_smul (x:=x) (pure_coordF a).smooth.contDiffAt a (2:ℝ),grad_coordF]; simp
  norm_num

lemma lap_coordF_mul (a : Axis) (hf : ContDiff ℝ ∞ f) (x : E4) :
    lap (coordF a • f) x = x a • lap f x + (2:ℝ) • grad a f x := by
  let L := ContinuousLinearMap.lsmul ℝ (E:=F) ℝ
  change lap (fun x => L (coordF a x) (f x)) x = _
  rw [lap_pair (pure_coordF a).smooth hf L x]
  change lap (coordF a) x • f x + x a • lap f x + (2:ℝ) • ∑ b : Axis, grad b (coordF a) x • grad b f x = _
  rw [lap_coordF]; simp [grad_coordF,ite_smul]

lemma lap_raise (hf : Pure j f) : lap (qRad • f) = (4*(2+(j:ℝ))) • f + qRad • lap f := by
  funext x; let L := ContinuousLinearMap.lsmul ℝ (E:=F) ℝ
  change lap (fun x => L (qRad x) (f x)) x = _
  rw [lap_pair pure_square.smooth hf.smooth L x,lap_square]
  change (8:ℝ) • f x + qRad x • lap f x + (2:ℝ) • ∑ a : Axis, grad a qRad x • grad a f x = (4*(2+(j:ℝ))) • f x + qRad x • lap f x
  simp_rw [grad_square,Pi.smul_apply,smul_eq_mul,mul_smul, ← Finset.smul_sum,coordF,hf.euler]; module
end calculus
end YM.Extra.FD.SphereTest
