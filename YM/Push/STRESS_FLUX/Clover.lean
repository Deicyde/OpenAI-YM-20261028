import YM.Push.STRESS_FLUX.Jets
import YM.Push.STRESS_FLUX.LinkD
import YM.Work.G02
import YM.Work.G03


/-!
# Signed clovers and price-force symbols through order three

Unmasked lattice constructions and their expansion on actual radial-gauge tests on the
cover. Orders in *link size h*, at h=0. No statement that typical Wilson configurations
have smooth expansions! (.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Lattice Wilson RG Labels Source Source.Drops Function Set Filter Gauge MeasureTheory Work
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {D : ℕ}

section Cover
variable {R : Type*} [AddCommGroup R] [One R]

def stencil {V : Type*} [AddCommGroup V] [Module ℝ V] (v : Step → Step → V) (a b : Axis) := (4:ℝ)⁻¹ •
    ((v (posDir a) (posDir b) - v (posDir a) (negDir b)) - (v (negDir a) (posDir b) - v (negDir a) (negDir b)))

def clover (U : Links R G.El) (x : Four R) := stencil (plate U x)
lemma clover_gauge (t : Four R → G.El) (U : Links R G.El) (x : Four R) (a b : Axis) : clover (gauge t U) x a b = G.adjoint (t x) (clover U x a b) := by simp [clover, stencil, plate_gauge]
lemma clover_pull (s : Signed) (z : Four R) (U : Links R G.El) (x : Four R) (a b : Axis) :
    clover (pull s z U) x a b = (sign s a * sign s b) • clover U (affine s z x) (s.perm a) (s.perm b) := by
  unfold clover stencil; simp_rw [plate_pull]; cases h₁ : s.flip a <;> cases h₂ : s.flip b <;>
    simp only [posDir,negDir,Step.rotate,sign,h₁,h₂,Bool.true_xor,Bool.false_xor,Bool.false_eq_true,reduceIte,
      Bool.not_true,Bool.not_false,one_mul,mul_one,neg_mul_neg,one_smul,neg_one_smul,← smul_neg] <;> (congr 1; abel)
lemma clover_swap (U : Links R G.El) (x : Four R) (a b : Axis) : clover U x a b = -clover U x b a := by
  unfold clover stencil; conv_lhs => simp only [plate_swap U x (posDir a) (posDir b),plate_swap U x (negDir a) (posDir b),
    plate_swap U x (posDir a) (negDir b),plate_swap U x (negDir a) (negDir b)]
  rw [← smul_neg]; congr 1; abel
end Cover
lemma clover_regular (x : Site n) (a b : Axis) : RegularD fun U : Config G n => clover U x a b :=
  (((regular_plate ..).sub (regular_plate ..)).sub ((regular_plate ..).sub (regular_plate ..))).scale _

section Calculus
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
lemma derivative_clm {f : ℝ → V} {k : ℕ} (h : ContDiffAt ℝ k f 0) (L : V →L[ℝ] W) : iteratedDeriv k (L ∘ f) 0 = L (iteratedDeriv k f 0) := by
  unfold iteratedDeriv; rw [L.iteratedFDeriv_comp_left h le_rfl]; rfl
lemma derivative_scale {f : ℝ → V} {k : ℕ} (h : ContDiffAt ℝ k f 0) (t : ℝ) :
    iteratedDeriv k (fun u => t • f u) 0 = t • iteratedDeriv k f 0 := iteratedDeriv_const_smul h t
private local instance zoomTaylorSMul (i : ℕ) : IsBoundedSMul ℝ (Taylor G i) := @NormedSpace.toIsBoundedSMul ℝ (Taylor G i) _ _ inferInstance
private local instance snapSMul (d : ℕ) : IsBoundedSMul ℝ (Snap G d) := @NormedSpace.toIsBoundedSMul ℝ _ _ _ inferInstance
private def zoom (D : ℕ) (A : Jet G) (h : ℝ) := trunk D (scaleJet A h)
private lemma zoom_zero (A : Jet G) : zoom D A 0 = 0 := by funext; simp [zoom,trunk, scaleJet]
private lemma zoom_smooth (A : Jet G) : ContDiff ℝ ω (zoom D A) := contDiff_pi.mpr fun _ => (contDiff_id.pow _).smul contDiff_const
private lemma zoom_deriv (A : Jet G) (k : ℕ) (j : Fin (D-1)) : (iteratedDeriv k (zoom D A) 0) j = if j.val+2=k then (k.factorial : ℝ) • A j.val else 0 := by
  have ht : ContDiffAt ℝ k (zoom D A) 0 := ((zoom_smooth A).contDiffAt).of_le le_top
  have he := derivative_clm (V:=Snap G D) (W:=Taylor G j.val) ht (ContinuousLinearMap.proj (R:=ℝ) (φ:= fun i : Fin (D-1) => Taylor G i.val) j)
  trans iteratedDeriv k (fun h : ℝ => h^(j.val+2) • A j.val) 0
  · exact he.symm
  rw [iteratedDeriv_smul_const (contDiffAt_id.pow (j.val+2)),iteratedDeriv_fun_pow_zero]; by_cases h : k=j.val+2
  · subst k; rw [if_pos rfl, if_pos rfl]
  rw [if_neg h,if_neg (Ne.symm h),Nat.cast_zero, zero_smul]

private lemma zoom_first (A : Jet G) : deriv (zoom D A) 0 = 0 := funext fun i => by
  rw [← iteratedDeriv_one]; exact (zoom_deriv A 1 i).trans (if_neg (by omega))
private def single (A : Jet G) (k : Fin (D-1)) : Snap G D := Pi.single k (A k.val)
private lemma zoom_next (A : Jet G) (k : Fin (D-1)) : iteratedDeriv (k.val+2) (zoom D A) 0 = ((k.val+2).factorial : ℝ) • single A k := by
  funext j; rw [zoom_deriv]; by_cases he:j=k
  · subst j; simp [single]
  have ht := mt Fin.ext he; simp [ht,Pi.single_eq_of_ne he,single]

variable [CompleteSpace V]
omit [CompleteSpace V] in
private lemma first_symbol (A : Jet G) {f : Snap G D → V} (hf : AnalyticAt ℝ f 0) : deriv (f ∘ zoom D A) 0 = 0 := by
  rw [fderiv_comp_deriv _ (by rw [zoom_zero]; exact hf.differentiableAt) ((zoom_smooth (D:=D) A).differentiable (by simp) (0:ℝ)),zoom_first,map_zero]
private lemma second_symbol (A : Jet G) {f : Snap G D → V} (hf : AnalyticAt ℝ f 0) (hd : 0 < D-1) : iteratedDeriv 2 (f ∘ zoom D A) 0 =
    2 • fderiv ℝ f 0 (single A ⟨0,hd⟩) := by
  rw [iteratedDeriv_vcomp_two (by rw [zoom_zero]; exact hf.contDiffAt.of_le le_top) ((zoom_smooth A).contDiffAt.of_le le_top),zoom_zero,zoom_first,
    show iteratedDeriv 2 (zoom D A) _ = _ from zoom_next A ⟨0,hd⟩,map_smul]
  simp [ContinuousMultilinearMap.map_coord_zero (iteratedFDeriv ℝ 2 f 0) (0:Fin 2) (m:=fun _ => 0) rfl,Nat.factorial]
  module
private lemma third_symbol (A : Jet G) {f : Snap G D → V} (hf : AnalyticAt ℝ f 0) (hd : 1 < D-1) : iteratedDeriv 3 (f ∘ zoom D A) 0 =
    6 • fderiv ℝ f 0 (single A ⟨1,hd⟩) := by
  rw [iteratedDeriv_vcomp_three (by rw [zoom_zero]; exact hf.contDiffAt.of_le le_top) ((zoom_smooth A).contDiffAt.of_le le_top),zoom_zero,zoom_first,
    show iteratedDeriv 3 (zoom D A) _ = _ from zoom_next A ⟨1,hd⟩,map_smul]
  simp [ContinuousMultilinearMap.map_coord_zero (iteratedFDeriv ℝ 3 f 0) (0:Fin 3) (m:=fun _ => 0) rfl,
    ContinuousMultilinearMap.map_coord_zero (iteratedFDeriv ℝ 2 f 0) (1:Fin 2) (m:=![(iteratedDeriv 2 (zoom D A) 0),0]) rfl,
    ContinuousMultilinearMap.map_coord_zero (iteratedFDeriv ℝ 2 f 0) (0:Fin 2) (m:=![0,(iteratedDeriv 2 (zoom D A) 0)]) rfl, Nat.factorial]
  module
end Calculus

section Walk
private def snapPlate (H : Hol G) (D : ℕ) (x : Cover) (a b : Step) (A : Snap G D) := plate (H.links D (expand D A) 1) x a b
set_option maxHeartbeats 600000 in
private lemma plate_symbol (H : Hol G) (D : ℕ) (x : Cover) (a b : Step) :
    AnalyticAt ℝ (snapPlate H D x a b) 0 ∧ ∀ J, fderiv ℝ (snapPlate H D x a b) 0 J = Exterior.linkSum (access J) x (Lattice.oriented a b) := by
  let L : G.Mat →L[ℝ] G.Color := G.projectColor.toContinuousLinearMap ∘L ((1/2:ℝ) • (ContinuousLinearMap.id ℝ _ - (starL' ℝ).toContinuousLinearMap))
  let f A := G.mat (travel (H.links D (expand D A) 1) x (Lattice.oriented a b))
  obtain ⟨ht,hb⟩ := G02.walkGerm H D (Lattice.oriented a b) x
  have he : AnalyticAt ℝ (L ∘ f) 0 := (L.analyticAt _).comp ht
  have hd : snapPlate H D x a b = L ∘ f := rfl
  rw [hd]; refine ⟨he, fun J => ?_⟩
  have hg := L.hasFDerivAt.comp_hasDerivAt 0 (hb J)
  letI : IsBoundedSMul ℝ (Snap G D) := @NormedSpace.toIsBoundedSMul ℝ _ _ _ inferInstance
  have hh : HasDerivAt (fun t : ℝ => t • J) J 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const J
  refine ((he.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hh (zero_smul ..).symm)).unique (hg.congr_deriv ?_)
  change G.projectColor ((1/2:ℝ) • (G.colorMat _ - star _)) = _
  rw [G.colorMat_skew,sub_neg_eq_add,← two_smul ℝ, smul_smul, div_mul_cancel₀ _ (by norm_num),one_smul,G.project_colorMat]

def flag (d : Step) : ℝ := if d.neg then -1 else 1
private lemma signed_square (x : Cover) (a b : Step) (f : Edge Cover → G.Color) :
    Exterior.linkSum f x (Lattice.oriented a b) = (flag a * flag b) • Exterior.linkSum f (atFace x a b) (square a.dir b.dir) := by
  rcases a with ⟨a,h|h⟩ <;> rcases b with ⟨b,t|t⟩ <;>
    simp [Lattice.oriented,square, atFace, flag, posDir, negDir, Step.rev, Step.vec, Step.used, Exterior.linkSum, add_right_comm x, sub_eq_add_neg] <;> abel_nf

open Work.G03
private lemma access_single (J : Jet G) (j : Fin (D-1)) (x : Cover) (a : Axis) : access (single J j) (x,a) = edgeInt (J j.val) a (castPos x) := by
  rw [edge_sum,← Fin.sum_univ_eq_sum_range, Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
  · simp [expand,single]
  intro i hi he
  have ht : expand D (single J j) i.val = 0 := by simp [expand,single,Pi.single_eq_of_ne he]
  simp only [ht]; change (∫ _ in (0 : ℝ)..1, (0 : G.Color)) = _; simp

private lemma plate_differential (H : Hol G) (J : Jet G) (k : Fin (D-1)) (x : Cover) (a b : Step) : fderiv ℝ (snapPlate H D x a b) 0 (single J k) =
    (flag a * flag b) • net (J k.val) a.dir b.dir (castPos (atFace x a b)) 1 := by
  rw [(plate_symbol ..).2,signed_square, square_sum, net,partial_eq_diff, partial_eq_diff]
  simp_rw [access_single,castPos_step]; congr 1; abel

def plateTest (H : Hol G) (D : ℕ) (J : Jet G) (x : Cover) (a b : Step) (t : ℝ) := plate (H.links D J t) x a b
private lemma plate_via_zoom (H : Hol G) (D : ℕ) (J : Jet G) (x : Cover) (a b : Step) : plateTest H D J x a b = snapPlate H D x a b ∘ zoom D J := by
  funext t; rw [plateTest,Drops.scales H]; rfl
lemma plate_smooth (H : Hol G) (D : ℕ) (J : Jet G) (x : Cover) (a b : Step) (k : WithTop ℕ∞) : ContDiffAt ℝ k (plateTest H D J x a b) 0 := by
  rw [plate_via_zoom]; apply ((show AnalyticAt ℝ _ _ from (by rw [zoom_zero]; exact (plate_symbol H D x a b).1)).contDiffAt.of_le le_top).comp 0 ((zoom_smooth J).contDiffAt.of_le le_top)
lemma plate_principal (H : Hol G) (J : Jet G) (x : Cover) (a b : Step) (hD : 2 ≤ D) :
    let f := plateTest H D J x a b
    f 0 = 0 ∧ deriv f 0 = 0 ∧ iteratedDeriv 2 f 0 = (2:ℝ) • (flag a * flag b) • curl0 a.dir b.dir (J 0) := by
  intro f
  refine ⟨?_,?_,?_⟩
  · simp only [f,plateTest,plate,H.flat D J,Pressure.one, G.curvature_unit]
  · dsimp only [f]; rw [plate_via_zoom]; exact first_symbol J (plate_symbol ..).1
  unfold f; rw [plate_via_zoom,second_symbol J (plate_symbol ..).1 (by omega),plate_differential]
  have he := scale_net (J 0) a.dir b.dir (castPos (atFace x a b)) 0
  rw [pow_zero,one_smul,zero_smul,net_at_zero] at he
  rw [← Nat.cast_smul_eq_nsmul ℝ, he.symm]; norm_num; rfl
lemma plate_subprincipal (H : Hol G) (J : Jet G) (x : Cover) (a b : Step) (hD : 3 ≤ D) :
    iteratedDeriv 3 (plateTest H D J x a b) 0 = (6:ℝ) • (flag a*flag b) • net (J 1) a.dir b.dir (castPos (atFace x a b)) 1 := by
  rw [plate_via_zoom,third_symbol J (plate_symbol ..).1 (by omega),plate_differential]; module

lemma net_shift (A : Taylor G 1) (a b : Axis) (x y : E4) : net A a b (x+y) 1 = net A a b x 1 + curled 1 y a b A := by
  have he (a b : Axis) (x z : E4) : Maxwell.grad a (A.value b) (x+z) = Maxwell.grad a (A.value b) x + Maxwell.grad a (A.value b) z := by
    unfold Maxwell.grad Analysis.D Taylor.value; simp only [Tensor.differential_diagonal _ (A.property.1 b)]
    let L := ContinuousMultilinearMap.ofSubsingleton ℝ E4 G.Color (0:Fin 1)
    obtain ⟨f,hf⟩ := L.surjective ((A.val b).curryLeft (basis a))
    rw [← hf]; change (1+1) • f (x+z) = (1+1) • f x + (1+1) • f z; rw [map_add, smul_add]
  have hh (a b : Axis) : meanPartial A a b (x+y) 1 = meanPartial A a b x 1 + Maxwell.grad a (A.value b) y := by
    have hc (s : ℝ) : Continuous (fun t : ℝ => Maxwell.grad a (A.value b) (x+(1*s) • basis b+(1*t) • basis a)) := (continuous_grad A a b).comp (show Continuous (fun t : ℝ => x+(1*s) • basis b+(1*t) • basis a) by fun_prop)
    have hd : Continuous (fun s : ℝ => ∫ t : ℝ in 0..1, Maxwell.grad a (A.value b) (x+(1*s) • basis b+(1*t) • basis a)) :=
      by apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'; exact ((continuous_grad A a b).comp (f:=fun p : ℝ × ℝ => x+(1*p.1) • basis b+(1*p.2) • basis a) (by fun_prop))
    unfold meanPartial; simp_rw [show ∀ s t : ℝ, x+y+(1*s) • basis b+(1*t) • basis a=x+(1*s) • basis b+(1*t) • basis a+y from fun s t => by abel,
      he a b (x+_+_) y, intervalIntegral.integral_add ((hc _).intervalIntegrable ..) intervalIntegrable_const,intervalIntegral.integral_const,sub_zero,one_smul,
      intervalIntegral.integral_add (hd.intervalIntegrable ..) intervalIntegrable_const,intervalIntegral.integral_const,sub_zero,one_smul]
  rw [net,hh,hh,curled_deriv,net]; abel
end Walk
