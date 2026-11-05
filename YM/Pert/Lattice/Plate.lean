import YM.Pert.Lattice.Recovery
/-! Transported oriented Wilson curvatures, local stencils and flat derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bare
open Lattice Function Filter Orb
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

section
variable {R : Type*} [AddCommGroup R] [One R]
/-- Curl of group holonomy based at shifted site, brought back by Wilson line. -/
def plateU (U : Lattice.Links R G.El) (x : Four R) (s : Walk) (i j : Axis) : G.Color :=
  G.adjoint (travel U x s) (G.curvature (travel U (stop x s) (square i j)))
lemma plate_gauge (t : Four R → G.El) (U : Lattice.Links R G.El) (x s i j) : plateU (gauge t U) x s i j = G.adjoint (t x) (plateU U x s i j) := by
  simp only [plateU,travel_gauge,square_stop,G.curvature_conjugate, G.adjoint_mul]
  rw [← G.adjoint_mul ((t _)⁻¹) (t _),inv_mul_cancel,G.adjoint_one]
lemma square_links (U : Lattice.Links R G.El) (x : Four R) (i j : Axis) :
    travel U x (square i j)=U (x,i)*U (x+step i,j)*(U (x+step j,i))⁻¹*(U (x,j))⁻¹ := by
  have he : x+step i+step j+(-(step i):Four R) = x+step j := by abel
  simp only [square,travel,Step.pos_read,Step.neg_read,Step.vec_neg,Step.vec_pos]; rw [he]; simp only [mul_one,add_sub_cancel_right,show x+step i+step j-step i=x+step j by abel]; group
end

def plate (x : Site n) (s : Walk) (i j : Axis) (a : Potential G n) := plateU (positiveLinks a) x s i j

lemma travel_flat (x : Site n) (s : Walk) : travel (positiveLinks (0:Potential G n)) x s = 1 := by
  induction s generalizing x with
  | nil => rfl
  | cons d s ih => rw [travel,ih]; cases h : d.neg <;> simp [Step.read,h]
@[simp] lemma plate_flat (x : Site n) (s i j) : plate (G:=G) x s i j 0=0 := by simp [plate,plateU,travel_flat]
lemma travel_mDiff (x : Site n) (s : Walk) : ContDiff ℝ ω (fun a => G.mat (travel (positiveLinks a) x s)) := by
  induction s generalizing x with
  | nil => exact contDiff_const
  | cons d s ih =>
    simp only [travel,Step.read,G.mat_mul]; cases h : d.neg
    · simp only [Bool.false_eq_true,↓reduceIte]; exact (pos_mDiff _).mul (ih _)
    · simp only [↓reduceIte]; exact (pInv_mDiff _).mul (ih _)
lemma curve_diff {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] {f : R → G.El} (h : ContDiff ℝ ω (fun x => G.mat (f x))) : ContDiff ℝ ω (fun x => G.curvature (f x)) := by
  unfold Gauge.curvature
  exact G.projectColor.toContinuousLinearMap.contDiff.comp (ContDiff.const_smul (1/2:ℝ) (h.sub ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp h)))
lemma plate_diff (x : Site n) (s : Walk) (i j : Axis) : ContDiffAt ℝ ω (plate (G:=G) x s i j) 0 := by
  unfold plate plateU; apply Push.Loops.adjoint_diff
  · exact (travel_mDiff ..).contDiffAt
  exact (curve_diff (travel_mDiff ..)).contDiffAt

lemma plate_deriv (x : Site n) (s : Walk) (i j : Axis) (v : Potential G n) :
    (fderiv ℝ (plate (G:=G) x s i j) 0) v = curL (stop x s) i j v := by
  let T (r : ℝ) := travel (positiveLinks (r • v)) x s
  let F (r : ℝ) := G.curvature (travel (positiveLinks (r • v)) (stop x s) (square i j))
  let A := G.mat ∘ T; let Z := star (A 0)
  have hT : T 0 = 1 := by simp [T,travel_flat]
  have hA : DifferentiableAt ℝ A 0 := (((travel_mDiff x s).differentiable (by simp)) ((0:ℝ) • v)).comp (f:=fun r => r • v) 0 ((show DifferentiableAt ℝ id (0:ℝ) from differentiableAt_id).smul (differentiableAt_const v))
  have hZ := hA.hasDerivAt.star
  have hD := Work.F03.curvature_of_hasDerivAt (plaq_diff (stop x s) i j v)
  have hF : HasDerivAt F (curL (stop x s) i j v) 0 := by simpa only [F, plaquette, square_links] using hD
  have hS := G.colorMat.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) hF
  have hH := G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) ((hA.hasDerivAt.mul hS).mul hZ)
  let W := fun r : ℝ => G.projectColor ((G.mat (T r)*G.colorMat (F r))*star (G.mat (T r)))
  have hw : HasDerivAt W (curL (stop x s) i j v) 0 := by
    convert! hH using 1; simp [F,A,hT,travel_flat,LinearMap.coe_toContinuousLinearMap]; exact (G.project_colorMat _).symm
  have he : W = fun r => plate x s i j (r • v) := by funext r; rfl
  have ht : HasDerivAt (fun r : ℝ => r • v) v 0 := by simpa using! (hasDerivAt_id' (0 : ℝ)).smul_const v
  have hv := (plate_diff (G:=G) x s i j).differentiableAt (by simp) |>.hasFDerivAt
  change HasFDerivAt (plate x s i j) (fderiv _ _ 0) 0 at hv
  nth_rw 2 [show (0:Potential G n) = (0:ℝ) • v by simp] at hv
  have H : HasDerivAt (fun r : ℝ => plate x s i j (r • v)) _ 0 := (hv.comp_hasDerivAt (l:=plate x s i j) (f:=fun r : ℝ => r • v) 0 ht)
  exact H.unique ((show HasDerivAt W _ _ from hw).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun r : ℝ => (congr_fun he r).symm)))
end YM.Pert.Bare
