import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Bid.Loan
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04
import YM.Work.B06

/-! # Real loop probes

Hessian of the *log*, at an actual invertible score,
in physical entry calculus (don't need compatible norms on matrix types).
E §loopt (§c2lp C12) / Precision.FreshDet. Signs use same external
order throughout. Needed on finite torus before period error.
Includes zero dimensional Free.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Jacobi
open Function Filter Finset Matrix
open scoped Topology BigOperators ContDiff
variable {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Type} [Fintype κ] [DecidableEq κ]

-- Directional fderiv rather than deriv along ray: even for mixed
abbrev blade (v : X) (f : X → E) (x : X) := fderiv ℝ f x v
abbrev mixed (v w : X) (f : X → E) := blade v (blade w f)

variable (v : X) {x : X}
lemma iter (w : X) {f : X → E} (hf : ContDiffAt ℝ ω f x) : mixed v w f x=iteratedFDeriv ℝ 2 f x ![v,w] := by
  let L := ContinuousLinearMap.apply ℝ E w
  have h : blade w f=L ∘ fderiv ℝ f := rfl
  unfold mixed
  rw [h, blade, fderiv_comp _ L.differentiableAt ((hf.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)), L.fderiv,iteratedFDeriv_two_apply]
  rfl

lemma smooth {f : X → E} (hf : ContDiffAt ℝ ω f x) : ContDiffAt ℝ ω (blade v f) x := by
  let L := ContinuousLinearMap.apply ℝ E v
  exact L.contDiff.contDiffAt.comp (f:=fderiv ℝ f) _ (hf.fderiv_right (m:=ω) (by simp))
lemma series {n : Type*} {S : Finset n} {F : n → X → E} (h : ∀ i∈S, ContDiffAt ℝ ω (F i) x) :
    blade v (fun y => ∑ i∈S, F i y) x=∑ i∈S, blade v (F i) x := by
  unfold blade; rw [fderiv_fun_sum (fun i hi => (h i hi).differentiableAt (by simp)),_root_.sum_apply]
lemma product {f g : X → ℝ} (hf : ContDiffAt ℝ ω f x) (hg : ContDiffAt ℝ ω g x) :
    blade v (fun y => f y*g y) x=f x * blade v g x +g x * blade v f x := by
  unfold blade; rw [fderiv_fun_mul (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))]; rfl
@[simp] lemma blade_const (y : E) : blade v (fun _ => y) x=0 := by unfold blade; simp

private lemma leaves {σ : Equiv.Perm κ} (h : σ≠1) (i : κ) : ∃ j∈univ.erase i, σ j≠j := by
  by_contra! ht
  simp only [mem_erase,mem_univ,and_true] at ht
  apply h; ext j; change σ j=j
  by_cases he : j=i
  · subst i; by_contra hh; exact hh (σ.injective (ht (σ j) hh) : _)
  exact ht _ he

variable {T B : X→Matrix κ κ ℝ}
def Faces (T : X→Matrix κ κ ℝ) (x : X) := ∀ i j, ContDiffAt ℝ ω (fun y => T y i j) x
def delta (v : X) (T : X→Matrix κ κ ℝ) (x : X) : Matrix κ κ ℝ := Matrix.of fun i j => blade v (fun y=> T y i j) x

lemma face_det (hf : Faces T x) : ContDiffAt ℝ ω (fun y => (T y).det) x := by
  simp_rw [det_apply']; exact ContDiffAt.sum fun i _=> contDiffAt_const.mul (contDiffAt_prod fun j _ => hf _ _)
omit [DecidableEq κ] in
lemma face_mul (hf : Faces T x) (hg : Faces B x) : Faces (fun y => T y*B y) x := by
  intro i j; simp_rw [mul_apply]; exact ContDiffAt.sum fun a _ => (hf _ _).mul (hg _ _)
omit [Fintype κ] [DecidableEq κ] in
lemma face_const (U : Matrix κ κ ℝ) : Faces (X:=X) (fun _ => U) x := fun _ _ => contDiffAt_const
omit [DecidableEq κ] in
lemma faces_near (hf : Faces T x) : ∀ᶠ y in 𝓝 x, Faces T y := by
  have h i j := (hf i j).eventually (by simp)
  simp only [Faces,eventually_all] at *; exact h
omit [DecidableEq κ] in
lemma triangle (hf : Faces T x) (hg : Faces B x) : delta v (fun y => T y*B y) x=T x * delta v B x + delta v T x * B x := by
  ext i j; unfold delta; simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [series v (fun k _=> (hf _ _).mul (hg _ _)),← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _=> ?_; rw [product v (hf ..) (hg ..), mul_comm (B _ _ _)]
omit [Fintype κ] in
lemma mag : delta v (fun _ => (1:Matrix κ κ ℝ)) x = 0 := by ext; simp [delta]

lemma dotRate (hg : Faces T x) (hf : T x=1) : blade v (fun y => (T y).det) x = Matrix.trace (delta v T x) := by
  let P (σ : Equiv.Perm κ) (y : X) := ∏ i, T y (σ i) i
  have he (σ) : ContDiffAt ℝ ω (P σ) x := contDiffAt_prod fun i _ => hg _ _
  simp_rw [det_apply']
  rw [series v (fun i _ => contDiffAt_const.mul (he i)),Finset.sum_eq_single_of_mem (1:Equiv.Perm κ) (Finset.mem_univ _), product v contDiffAt_const (he _)]
  · simp only [map_one, Units.val_one, Int.cast_one, one_mul, blade_const, mul_zero, add_zero]
    unfold blade
    rw [fderiv_finsetProd (fun i _ => (hg _ _).differentiableAt (by simp)),_root_.sum_apply]
    simp only [hf,Equiv.Perm.one_apply,one_apply_eq,Finset.prod_const_one, one_smul]; rfl
  intro σ _ hx; rw [product v contDiffAt_const (he _), blade_const (v:=v), mul_zero, add_zero]
  unfold blade; rw [fderiv_finsetProd (fun i _ => (hg _ _).differentiableAt (by simp)),_root_.sum_apply]
  rw [Finset.sum_eq_zero, mul_zero]
  intro i _; obtain ⟨j,hj,hh⟩ := leaves hx i
  rw [Finset.prod_eq_zero hj (by rw [hf,one_apply_ne hh]), zero_smul]; rfl

lemma solid (hg : Faces T x) (hf : (T x).det≠0) : blade v (fun y => (T y).det) x = (T x).det*Matrix.trace ((T x)⁻¹ * delta v T x) := by
  let A := (T x)⁻¹
  have hh : IsUnit (T x).det := isUnit_iff_ne_zero.mpr hf
  have ht := dotRate v (face_mul (face_const A) hg) (Matrix.nonsing_inv_mul _ hh)
  have he (y : X) : (A*T y).det = A.det*(T y).det := det_mul ..
  simp_rw [he] at ht
  rw [product v contDiffAt_const (face_det hg)] at ht
  have hx := triangle v (face_const A) hg
  have hA : delta v (fun _ => A) x=0 := by ext; simp [delta]
  rw [hx,hA,zero_mul,add_zero,blade_const,mul_zero,add_zero] at ht
  calc
    _ = ((T x).det*A.det)*blade v (fun y => (T y).det) x := by rw [← det_mul, Matrix.mul_nonsing_inv _ hh, det_one,one_mul]
    _ = _ := by rw [mul_assoc,ht]
lemma stroke (hg : Faces T x) (hf : (T x).det≠0) : blade v (fun y => Real.log (T y).det) x=Matrix.trace ((T x)⁻¹ * delta v T x) := by
  have h := (Real.hasDerivAt_log hf).comp_hasFDerivAt x ((face_det hg).differentiableAt (by simp)).hasFDerivAt
  have ht := solid v hg hf
  calc
    _ = (T x).det⁻¹*blade v (fun y => (T y).det) x := by
      unfold blade; rw [show (fun y => Real.log (T y).det) = Real.log ∘ (fun y => (T y).det) from rfl,h.fderiv]; rfl
    _ = _ := by rw [ht]; field_simp

lemma face_inv (hg : Faces T x) (hf : (T x).det≠0) : Faces (fun y => (T y)⁻¹) x := by
  intro i j; simp_rw [Matrix.inv_def, Ring.inverse_eq_inv',Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  apply ContDiffAt.mul ((face_det hg).inv hf)
  apply face_det (κ:=κ)
  intro r s
  by_cases h : r=j
  · subst r; simp only [updateRow_self]; exact contDiffAt_const
  simpa only [updateRow_ne h] using hg r s

lemma flake (hg : Faces T x) (hf : (T x).det≠0) : delta v (fun y => (T y)⁻¹) x = -((T x)⁻¹ * delta v T x*(T x)⁻¹) := by
  let C := (T x)⁻¹; let D := delta v (fun y => (T y)⁻¹) x
  have ht : (fun y => (T y)⁻¹*T y) =ᶠ[𝓝 x] 1 := by
    filter_upwards [(face_det hg).continuousAt.eventually_ne hf] with y hy
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hy)
  have h : C*delta v T x+D*T x=delta v (fun _=>1) x := by
    rw [show _ + _ = _ from (triangle v (face_inv hg hf) hg).symm]; ext i j
    unfold delta blade; rw [of_apply,of_apply]
    exact congr_arg (fun F : X →L[ℝ] ℝ => F v) ((ht.fun_comp (fun S => S i j)).fderiv_eq)
  rw [mag v] at h
  have he := Matrix.mul_nonsing_inv (T x) (isUnit_iff_ne_zero.mpr hf)
  have hx := congr_arg (fun K => K*C) h
  rw [add_mul,zero_mul,mul_assoc D,he,mul_one] at hx
  rw [add_eq_zero_iff_eq_neg] at hx
  rw [hx,neg_neg]

omit [DecidableEq κ] in
lemma face_trace (hg : Faces T x) : ContDiffAt ℝ ω (fun y=>(T y).trace) x :=
  ContDiffAt.sum fun i _=> hg i i
omit [DecidableEq κ] in
lemma flutter (hg : Faces T x) : blade v (fun y=> (T y).trace) x = (delta v T x).trace :=
  series v fun i (_:i∈univ) => (hg i i)
omit [Fintype κ] [DecidableEq κ] in
lemma face_delta (hg : Faces T x) : Faces (delta v T) x := fun i j => smooth v (hg i j)

-- one of the two contractions (C12); real arbitrary +/-; includes same waves
lemma tranche (w : X) (hg : Faces T x) (hf : (T x).det≠0) : mixed v w (fun y => Real.log (T y).det) x =
    Matrix.trace ((T x)⁻¹*delta v (delta w T) x) - Matrix.trace ((T x)⁻¹*delta v T x*(T x)⁻¹*delta w T x) := by
  have hh : blade w (fun y => Real.log (T y).det) =ᶠ[𝓝 x] fun y => ((T y)⁻¹ * delta w T y).trace := by
    filter_upwards [faces_near hg,(face_det hg).continuousAt.eventually_ne hf] with y hy ht
    exact stroke w hy ht
  let K (y : X) := (T y)⁻¹*delta w T y
  have hT := face_inv hg hf
  have hx := face_mul hT (face_delta w hg)
  have he := flutter v hx
  have hv := triangle v hT (face_delta w hg)
  unfold mixed blade; rw [hh.fderiv_eq]
  change blade v (fun y => (K y).trace) x = _
  rw [show blade .. = _ from he,hv,flake v hg hf]; simp [sub_eq_add_neg]
end YM.Further.PhysicalPeriodLimitF933.Jacobi
