import YM.Extra.FREE_DETECTOR_ALGEBRA.Harmonic

set_option warningAsError false

/-!
# Action on the two indices and radial reflection

The latter acts ALSO on directions of all derivative indices when applied
to a whole jet label. Ordinary, real O(4).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {F : Type*}
abbrev Rank2 (F : Type*) := Axis → Axis → F

/-- Matrix times axis column of F. -/
def monoForm [AddCommGroup F] [Module ℝ F] (A : M4) : (Axis → F) →ₗ[ℝ] Axis → F where
  toFun v := fun i => ∑ a : Axis, A i a • v a
  map_add' v w := by ext i; simp [smul_add,Finset.sum_add_distrib]
  map_smul' c v := by ext i; simp [Finset.smul_sum,smul_comm c]

theorem mono_eval [AddCommGroup F] [Module ℝ F] (A : M4) (v : Axis → F) (i : Axis) :
    monoForm A v i = ∑ a : Axis, A i a • v a := rfl

theorem mono_mul [AddCommGroup F] [Module ℝ F] (A B : M4) (v : Axis → F) :
    monoForm (A * B) v = monoForm A (monoForm B v) := by
  ext i
  simp_rw [mono_eval,Matrix.mul_apply,Finset.sum_smul,mul_smul,Finset.smul_sum]
  rw [Finset.sum_comm]

@[simp] theorem mono_one [AddCommGroup F] [Module ℝ F] (v : Axis → F) : monoForm 1 v = v := by
  ext i; simp [mono_eval,Matrix.one_apply,ite_smul]

def bi [AddCommGroup F] [Module ℝ F] (A : M4) : Rank2 F →ₗ[ℝ] Rank2 F where
  toFun v i m := ∑ a : Axis, ∑ b : Axis, A i a • A m b • v a b
  map_add' v w := by ext i m; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext i m; simp [smul_comm c, Finset.smul_sum]

theorem bi_eval [AddCommGroup F] [Module ℝ F] (A : M4) (v : Rank2 F) (i m : Axis) :
    bi A v i m = ∑ a : Axis, ∑ b : Axis, A i a • A m b • v a b := rfl

@[simp] theorem bi_one [AddCommGroup F] [Module ℝ F] (v : Rank2 F) : bi 1 v = v := by
  ext i m; simp [bi_eval,Matrix.one_apply,ite_smul]

theorem bi_mul [AddCommGroup F] [Module ℝ F] (A B : M4) (v : Rank2 F) : bi (A*B) v = bi A (bi B v) := by
  ext i m
  simp_rw [bi_eval,Matrix.mul_apply, Finset.sum_smul,mul_smul,Finset.smul_sum]
  let f (a b x y : Axis) := A i x • A m y • B x a • B y b • v a b
  simp_rw [show ∀ a b x y, A i x • B x a • A m y • B y b • v a b = f a b x y from
    fun a b x y => by rw [smul_comm (B x a)]]
  change ∑ a : Axis, ∑ b : Axis, ∑ x : Axis, ∑ y : Axis, f a b x y =
    ∑ x : Axis, ∑ y : Axis, ∑ a : Axis, ∑ b : Axis, f a b x y
  rw [show (∑ a : Axis, ∑ b : Axis, ∑ x : Axis, ∑ y : Axis, f a b x y) =
    (∑ p : Axis × Axis, ∑ q : Axis × Axis, f p.1 p.2 q.1 q.2) by simp_rw [Fintype.sum_prod_type]]
  rw [Finset.sum_comm]; simp_rw [Fintype.sum_prod_type]

theorem inv_at (s : Ortho) (i m : Axis) : s⁻¹.val i m = s.val m i := rfl

theorem rowId (s : Ortho) (i j : Axis) : ∑ k, s.val k i * s.val k j = if i=j then 1 else 0 :=
  Eq.trans (congr_arg (fun A : M4 => A i j) s.transp) (Matrix.one_apply ..)

/-- Matrix of radial reflection (normal x). If x=0 this convention uses I. -/
def faceM (x : E4) : M4 := Matrix.of fun i j => (if i=j then 1 else 0) - (2*rr x*x i*x j)

theorem real_dot (x y : E4) : ∑ j : Axis, x j * y j = ⟪x,y⟫ := by
  rw [← real_inner_comm x, PiLp.inner_apply]; simp [RCLike.inner_apply]

theorem faceM_act (x y : E4) : M4.move (faceM x) y = y - (2 * rr x * ⟪x,y⟫) • x := by
  ext i
  rw [M4.at_coord]
  simp only [faceM,Matrix.of_apply]
  simp_rw [sub_mul, Finset.sum_sub_distrib, mul_assoc (2*rr x*x i), ← Finset.mul_sum,
    show ∑ j : Axis, x j*y j = _ from real_dot x y,ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
  change y i - (2 * rr x * x i * ⟪x,y⟫) = y i - (2 * rr x * ⟪x,y⟫)*x i
  ring

private lemma twiceFace (x y : E4) : M4.move (faceM x) (M4.move (faceM x) y) = y := by
  by_cases he : x = 0
  · rw [faceM_act, faceM_act]; simp [he]
  have ht : rr x * ⟪x,x⟫ = 1 := by rw [real_inner_self_eq_norm_sq]; exact inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr he))
  rw [faceM_act, faceM_act, inner_sub_right,real_inner_smul_right]
  rw [show (2 * rr x * ⟪x,y⟫) * ⟪x,x⟫ = 2 * ⟪x,y⟫ by linear_combination 2 * ⟪x,y⟫ * ht]
  module

theorem faceM_symm (x : E4) : star (faceM x) = faceM x := by
  ext i m; simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial,faceM,Matrix.of_apply]
  by_cases he : i=m
  · subst m; rfl
  rw [if_neg he, if_neg (Ne.symm he)]; ring

theorem faceM_sq (x : E4) : faceM x * faceM x = 1 := by
  ext i m
  have he := M4.move_basis (faceM x*faceM x) i m
  rw [M4.move_mul,twiceFace] at he
  rw [← he]
  simp [Matrix.one_apply]

def face (x : E4) : Ortho := ⟨faceM x,by rw [faceM_symm, faceM_sq],by rw [faceM_symm, faceM_sq]⟩

@[simp] theorem face_inv (x : E4) : (face x)⁻¹ = face x := Subtype.ext (faceM_symm x)

theorem face_apply (x y : E4) : Ortho.move (face x) y = y - (2*rr x*⟪x,y⟫) • x := faceM_act x y

@[simp] theorem face_negates (x : E4) : Ortho.move (face x) x = -x := by
  rw [face_apply, real_inner_self_eq_norm_sq]
  by_cases he : x=0
  · simp [he]
  rw [mul_assoc,show rr x*‖x‖^2 = 1 from inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr he)),mul_one,two_smul]
  abel

lemma rr_move (s : Ortho) (x : E4) : rr (Ortho.move s x) = rr x := by unfold rr; rw [Ortho.move_norm]

theorem face_rotate (s : Ortho) (x : E4) : face (Ortho.move s x) * s = s * face x := by
  apply Ortho.ext; intro y
  rw [Ortho.move_mul,Ortho.move_mul,face_apply,face_apply,rr_move]
  change Ortho.motion s y - (2 * rr x*⟪_,_⟫) • _ = Ortho.motion s _
  rw [map_sub,map_smul]
  rw [show ⟪Ortho.move s x, Ortho.move s y⟫ = ⟪x,y⟫ from (Ortho.motion s).inner_map_map ..]; rfl

lemma bi_lr [AddCommGroup F] [Module ℝ F] (s : M4) (v : Rank2 F) (a b : Axis) : bi s v a b =
    monoForm s (fun i => monoForm s (v i) b) a := by simp_rw [bi_eval,mono_eval,Finset.smul_sum]

lemma face_column [AddCommGroup F] [Module ℝ F] (v : Axis → F) (x : E4) (i : Axis) : monoForm (faceM x) v i =
    v i - (2*rr x*x i) • ∑ a : Axis, (x a) • (v a) := by
  simp only [mono_eval,faceM,Matrix.of_apply, sub_smul,mul_smul,Finset.sum_sub_distrib]
  simp_rw [← Finset.smul_sum,ite_smul,one_smul, zero_smul]; simp

lemma anti_face [AddCommGroup F] [Module ℝ F] (v : Rank2 F) (ha : ∀ a b, v a b = - v b a) (x : E4) (i m : Axis) :
    let y := fun m => ∑ a : Axis, (x a) • v a m
    bi (face x).val v i m = v i m - (2*rr x) • (x i • y m - x m • y i) := by
  intro y
  have hv : (∑ m : Axis, x m • y m) = 0 := by
    let t := ∑ m : Axis, x m • y m
    change t = 0
    have he : t = -t := by
      unfold t y; simp_rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by nth_rw 1 [ha a b]; rw [smul_neg,smul_neg,smul_comm]
    have ht : (2:ℝ) • t = 0 := by rw [two_smul]; nth_rw 1 [he]; simp
    exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
  have he (a) : monoForm (faceM x) (v a) m = v a m + (2*rr x*x m) • y a := by
    rw [face_column,show ∑ b : Axis, x b • v a b = - y a by
      unfold y; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro b _; nth_rw 1 [ha a b]; rw [smul_neg]]
    rw [smul_neg,sub_neg_eq_add]
  rw [bi_lr]
  change monoForm (faceM x) (fun a => monoForm (faceM x) (v a) m) i = _
  simp_rw [he,face_column,smul_add, Finset.sum_add_distrib,
    fun i => smul_comm (x i) (2*rr x*x m) (y i),← Finset.smul_sum, hv, smul_zero,add_zero]
  change v i m + _ - _ • y m = _
  module
end YM.Extra.FD
