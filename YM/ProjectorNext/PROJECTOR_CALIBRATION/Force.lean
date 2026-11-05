import YM.Next.SCHEDULE.Stadium
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Gradient

/-! # Sampling energy gradients on the cover

Each sample is color at the anchor, including real connectors. Prove the
linearized response formula **on the actual holonomy tests**, in physical
color, using G02 link/slot results. -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Source.Drops Labels Work Function Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge}

abbrev Position := Edge Cover
abbrev base (x : Position) := route 0 x.1 1

/-- Cover samples: ordinary positive-link derivatives of energy after a fixed
connector to the anchor. -/
def sample (U : CoverConfig G) (x : Position) : G.Color :=
    G.adjoint (travel U 0 (base x)) (gradient U x.1 x.2)

lemma sample_gauge (U : CoverConfig G) (t : Cover → G.El) (x : Position) :
    sample (gauge t U) x = G.adjoint (t 0) (sample U x) := by
  simp_rw [sample, gradient_gauge,travel_gauge,route_end, G.adjoint_mul, ← G.adjoint_mul (t _)⁻¹ (t _)]
  simp

abbrev native (H : Hol G) (d : ℕ) (A : Snap G d) := H.links d (expand d A) 1

lemma native_one (H : Hol G) (d : ℕ) : native H d 0 = 1 := funext fun i => (G02.linkGerm H d i).2.1

lemma staple_one {R : Type*} [AddCommGroup R] [One R] (x : Four R) (ν : Axis) (q : PlaqAxes) :
    staple (1 : Links R G.El) ν x q = 0 := by
  simp [staple,cornerB,cornerC,faceValue,square,travel]

lemma sample_one (x : Position) : sample (1 : CoverConfig G) x = 0 := by
  simp [sample,gradient,staple_one]

section Adjoint
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_star {c : WithTop ℕ∞} {f : E → G.Mat} {x : E} (h : ContDiffAt ℝ c f x) :
    ContDiffAt ℝ c (fun y => star (f y)) x :=
  ((starL' ℝ (A:=G.Mat)).contDiff.contDiffAt.comp x h)

lemma color_contDiff {c : WithTop ℕ∞} {f : E → G.El} {x : E} (hf : ContDiffAt ℝ c (fun y => G.mat (f y)) x) :
    ContDiffAt ℝ c (fun y => G.curvature (f y)) x := by
  simp only [Gauge.curvature,G.mat_inv]
  change ContDiffAt ℝ c (fun y => G.projectColor.toContinuousLinearMap _) x
  exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=fun y => (1/2 : ℝ) • (G.mat (f y)-star (G.mat (f y)))) x
    ((contDiffAt_const (c:=(1/2:ℝ))).smul (hf.sub (contDiffAt_star hf)))

lemma ad_contDiff {c : WithTop ℕ∞} {f : E → G.El} {g : E → G.Color} {x : E}
    (hf : ContDiffAt ℝ c (fun y => G.mat (f y)) x) (hg : ContDiffAt ℝ c g x) :
    ContDiffAt ℝ c (fun y => G.adjoint (f y) (g y)) x := by
  let L := G.projectColor.toContinuousLinearMap
  let P := G.colorMat.toContinuousLinearMap
  change ContDiffAt ℝ c (fun y => L (G.mat (f y)*P (g y)*star (G.mat (f y)))) x
  exact L.contDiff.contDiffAt.comp (f:=fun y => G.mat (f y)*P (g y)*star (G.mat (f y))) x
    ((hf.mul (P.contDiff.contDiffAt.comp x hg)).mul (contDiffAt_star hf))

lemma ad_deriv {f : ℝ → G.El} {g : ℝ → G.Color} {u : G.Mat} {v : G.Color} (hf' : f 0 = 1) (hg' : g 0 = 0)
    (hf : HasDerivAt (fun t => G.mat (f t)) u 0) (hg : HasDerivAt g v 0) :
    HasDerivAt (fun t => G.adjoint (f t) (g t)) v 0 := by
  let L := G.projectColor.toContinuousLinearMap
  let P := G.colorMat.toContinuousLinearMap
  have H := L.hasFDerivAt.comp_hasDerivAt 0 ((hf.mul (P.hasFDerivAt.comp_hasDerivAt 0 hg)).mul hf.star)
  apply H.congr_deriv; dsimp only [comp_apply,Pi.mul_apply]; simp [hf',hg',P,L]
  exact G.project_colorMat _

lemma color_deriv {f : ℝ → G.El} {v : G.Color}
    (hf : HasDerivAt (fun t => G.mat (f t)) (G.colorMat v) 0) :
    HasDerivAt (fun t => G.curvature (f t)) v 0 := by
  let L := G.projectColor.toContinuousLinearMap
  simp_rw [Gauge.curvature,G.mat_inv]
  apply (L.hasFDerivAt.comp_hasDerivAt (0:ℝ) ((hf.sub hf.star).const_smul (1/2:ℝ))).congr_deriv
  rw [G.colorMat_skew,sub_neg_eq_add,← two_smul ℝ,smul_smul,div_mul_cancel₀ _ two_ne_zero,one_smul]
  exact G.project_colorMat _
end Adjoint

section Linear
variable {d : ℕ} (H : Hol G)

lemma staple_smooth (x : Cover) (ν : Axis) (q : PlaqAxes) :
    ContDiffAt ℝ ω (fun A : Snap G d => staple (native H d A) ν x q) 0 := by
  have h1 (y : Cover) : ContDiffAt ℝ ω (fun A : Snap G d => G.mat (faceValue (native H d A) (y,q))) 0 :=
    (G02.walkGerm H d (square q.val.1 q.val.2) y).1.contDiffAt
  have h2 (y : Cover) (l : Axis) := (G02.linkGerm H d (y,l)).1.contDiffAt (n:=ω)
  have h3 (y : Cover) (l : Axis) : ContDiffAt ℝ ω (fun A => G.mat ((native H d A (y,l))⁻¹ * faceValue (native H d A) (y,q) * native H d A (y,l))) 0 := by
    simp_rw [G.mat_mul,G.mat_inv]
    exact (((contDiffAt_star (G:=G) (h2 y l)).mul (h1 y)).mul (h2 y l))
  unfold staple
  refine ContDiffAt.add ?_ ?_
  all_goals split
  · exact (color_contDiff (h1 x)).sub (color_contDiff (h3 _ _))
  · exact contDiffAt_const
  · exact (color_contDiff (h3 _ _)).sub (color_contDiff (h1 x))
  · exact contDiffAt_const

lemma sample_smooth (x : Position) : ContDiffAt ℝ ω (fun A : Snap G d => sample (native H d A) x) 0 := by
  unfold sample gradient
  exact ad_contDiff (G02.walkGerm H d (base x) 0).1.contDiffAt
    (ContDiffAt.sum fun i _ => staple_smooth H _ _ i)

def linearFace (A : Snap G d) (x : Cover) (q : PlaqAxes) :=
    Exterior.linkSum (access A) x (square q.val.1 q.val.2)

def delta (F : Cover → PlaqAxes → G.Color) (x : Cover) (ν : Axis) (q : PlaqAxes) : G.Color :=
    (if q.val.1=ν then F x q - F (x-step q.val.2) q else 0) +
    (if q.val.2=ν then F (x-step q.val.1) q - F x q else 0)

set_option maxHeartbeats 400000 in
lemma staple_linear (A : Snap G d) (x : Cover) (ν : Axis) (q : PlaqAxes) :
    HasDerivAt (fun t : ℝ => staple (native H d (t • A)) ν x q) (delta (linearFace A) x ν q) 0 := by
  have h1 (y : Cover) : HasDerivAt (fun t : ℝ => G.curvature (faceValue (native H d (t • A)) (y,q)))
      (linearFace A y q) 0 := color_deriv ((G02.walkGerm H d (square q.val.1 q.val.2) y).2 A)
  have h2 (y : Cover) (l : Axis) := ((G02.linkGerm H d (y,l)).2.2 A).star
  have h3 (y : Cover) (l : Axis) : HasDerivAt (fun t : ℝ => G.curvature
      ((native H d (t • A) (y,l))⁻¹ * faceValue (native H d (t • A)) (y,q) * native H d (t • A) (y,l)))
      (linearFace A y q) 0 := by
    have hh (u z : G.El) : G.curvature (u⁻¹*z*u)=G.adjoint u⁻¹ (G.curvature z) := by
      simpa only [inv_inv] using G.curvature_conjugate u⁻¹ z
    simp_rw [hh]
    refine ad_deriv (by simp only [zero_smul,native_one, Pi.one_apply,inv_one]) ?_
      (u:=star (G.colorMat (access A (y,l)))) ?_ (h1 _)
    · simp [native_one,faceValue,square,travel]
    simp_rw [G.mat_inv]; exact h2 y l
  unfold staple delta
  split_ifs
  all_goals first
    | exact ((h1 _ |>.sub (h3 _ _)).add ((h3 _ _).sub (h1 _)))
    | exact ((h1 _ |>.sub (h3 _ _)).add (by exact hasDerivAt_const (0:ℝ) (0:G.Color)))
    | exact (hasDerivAt_const (0:ℝ) (0:G.Color)).add ((h3 _ _).sub (h1 _))
    | simp; exact hasDerivAt_const ..

lemma sample_linear (A : Snap G d) (x : Position) :
    HasDerivAt (fun t : ℝ => sample (native H d (t • A)) x) (∑ q, delta (linearFace A) x.1 x.2 q) 0 := by
  refine ad_deriv ?_ ?_ ((G02.walkGerm H d (base x) 0).2 A) (HasDerivAt.fun_sum (u:=Finset.univ) fun i _ => staple_linear H A x.1 x.2 i)
  · simp only [zero_smul,native_one]; exact Pressure.one _
  simp [gradient, native_one,staple_one]

def linearSample (d : ℕ) (x : Position) := fderiv ℝ (fun A => sample (native H d A) x) 0

set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 400000 in
lemma linearSample_eq (A : Snap G d) (x : Position) :
    linearSample H d x A = ∑ q, delta (linearFace A) x.1 x.2 q := by
  have hd : HasDerivAt (fun t : ℝ => t • A) A 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const A
  have he : HasDerivAt (fun t : ℝ => sample (native H d (t • A)) x) (linearSample H d x A) 0 :=
    (sample_smooth (d:=d) H x).differentiableAt (by simp) |>.hasFDerivAt |>.comp_hasDerivAt_of_eq (0:ℝ) hd (by simp)
  exact he.unique (sample_linear H A x)
end Linear
end YM.ProjectorNext.Calibration
