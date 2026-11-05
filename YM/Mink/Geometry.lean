import YM.Space.Orthogonal

/-!
# Timelike geometry & Euclidean coordinate pairing

Time last component everywhere in full/spatial indices.
Quadratic form m. (No unit setting or speed of light choices later.)
Pair position to dual frequencies by ordinary REAL Euclidean inner, as in
in these coordinates the forward cone is self-dual. Do not test
forward spectrum by reversing this convention on the time component.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Mink
open Set Filter Function
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators

def clockL : E4 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := time, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

def restL : E4 →L[ℝ] Space3 := LinearMap.toContinuousLinearMap
  { toFun := spatial, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[simp] theorem clockL_at (x) : clockL x = time x := rfl
@[simp] theorem restL_at (x) : restL x = spatial x := rfl

@[fun_prop] theorem clock_cont : Continuous time := clockL.continuous
@[fun_prop] theorem rest_cont : Continuous spatial := restL.continuous
@[simp] theorem clock_add (x y) : time (x+y)=time x+time y := map_add clockL x y
@[simp] theorem clock_mul (x) (t : ℝ) : time (t • x)=t*time x := map_smul clockL t x
@[simp] theorem clock_neg (x) : time (-x)=-time x := map_neg clockL x
@[simp] theorem rest_add (x y) : spatial (x+y)=spatial x+spatial y := map_add restL x y
@[simp] theorem rest_mul (x) (t : ℝ) : spatial (t • x)=t • spatial x := map_smul restL t x
@[simp] theorem rest_neg x : spatial (-x) = -spatial x := map_neg restL x
@[simp] theorem clock_zero : time 0 = 0 := map_zero clockL
@[simp] theorem rest_zero : spatial 0 = 0 := map_zero restL

/-- Coordinates interconvert continuously; volume assertion below. -/
def divide : E4 ≃L[ℝ] Space3 × ℝ := LinearEquiv.toContinuousLinearEquiv
  { toFun p := (spatial p, time p)
    invFun p := position p.1 p.2
    map_smul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    left_inv := position_eta
    right_inv := fun _ => by simp }

@[simp] theorem divide_at x : divide x = (spatial x,time x) := rfl
@[simp] theorem combine_at x t : divide.symm (x,t) = position x t := rfl

theorem ext_by {x y : E4} (hs : spatial x=spatial y) (ht : time x=time y) : x=y :=
  divide.injective (by rw [divide_at,divide_at,hs,ht])

@[simp] lemma roll_clock : time (basis timeAxis)=1 := by simp [time]
@[simp] lemma roll_space : spatial (basis timeAxis)=0 := by
  ext i; simp [spatial, basis_eq]

lemma pairing (x y : E4) : inner ℝ x y = inner ℝ (spatial x) (spatial y) + time x * time y := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Fin.sum_univ_castSucc]
  simp only [time,spatial, WithLp.ofLp_toLp]; congr 1
  simp [timeAxis, mul_comm]

lemma squares (x : E4) : ‖x‖^2 = ‖spatial x‖^2 + time x^2 := by
  rw [← real_inner_self_eq_norm_sq, pairing]; simp [pow_two]

def divide₂ : E4 ≃ₗᵢ[ℝ] WithLp 2 (Space3 × ℝ) where
  toLinearEquiv := divide.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Space3 × ℝ)).symm
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2]
    change ‖spatial x‖^2 + ‖time x‖^2 = _
    simpa using (squares x).symm

open MeasureTheory

theorem volume_divide : MeasurePreserving divide volume volume :=
    (WithLp.volume_preserving_ofLp _ _).comp divide₂.measurePreserving

def m (x : E4) := time x ^ 2 - ‖spatial x‖^2
def cone := {x | ‖spatial x‖ ≤ time x}
def inside := {x | ‖spatial x‖ < time x}
def spacelike := {x | m x < 0}

@[fun_prop] lemma cont_m : Continuous m := by unfold m; fun_prop
lemma closed_cone : IsClosed cone := isClosed_le (by fun_prop) (by fun_prop)
lemma open_inside : IsOpen inside := isOpen_lt (by fun_prop) (by fun_prop)
lemma open_spacelike : IsOpen spacelike := isOpen_lt (by fun_prop) continuous_const

lemma cone_self (x : E4) : x ∈ cone ↔ 0 ≤ time x ∧ 0 ≤ m x := by
  unfold m
  constructor
  · intro h
    exact ⟨(norm_nonneg _).trans h,sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) h _)⟩
  rintro ⟨h,H⟩
  exact le_of_sq_le_sq (sub_nonneg.mp H) h

lemma strict_self (x : E4) : x ∈ inside ↔ 0 < time x ∧ 0 < m x := by
  unfold m
  constructor
  · intro h
    exact ⟨lt_of_le_of_lt (norm_nonneg _) h, sub_pos.mpr (pow_lt_pow_left₀ h (norm_nonneg _) (by norm_num))⟩
  rintro ⟨h,H⟩
  exact (sq_lt_sq₀ (norm_nonneg _) h.le).mp (sub_pos.mp H)

lemma lateral (x : E4) : x ∈ spacelike ↔ |time x| < ‖spatial x‖ := by
  change _-_ < (0 : ℝ) ↔ _
  rw [sub_neg, ← sq_lt_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs]

lemma self_pair {x p : E4} (hx : x ∈ cone) (hp : p ∈ cone) : 0 ≤ inner ℝ x p := by
  rw [pairing]
  have he := (abs_le.mp (abs_real_inner_le_norm (spatial x) (spatial p))).1
  have hh := mul_le_mul (show ‖spatial x‖ ≤ _ from hx) (show ‖spatial p‖ ≤ _ from hp) (norm_nonneg _) ((cone_self _).1 hx).1
  linarith

lemma cone_test (x : E4) : x ∈ cone ↔ ∀ p ∈ cone, 0 ≤ inner ℝ x p := by
  constructor
  · exact fun hx _ hp => self_pair hx hp
  intro H
  by_cases h : ‖spatial x‖=0
  · have he := H (position 0 1) (by simp [cone]); rw [pairing] at he
    change ‖spatial x‖ ≤ _; simpa [h] using he
  let e := position (- ‖spatial x‖⁻¹ • spatial x) 1
  have hp : e ∈ cone := by
    have hh : 0 < ‖spatial x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    simp [e,cone,norm_smul,h]
  have he := H _ hp
  rw [pairing] at he
  simp only [e, spatial_position,time_position,inner_smul_right, real_inner_self_eq_norm_sq, mul_one] at he
  rw [pow_two,← mul_assoc (- _), neg_mul,inv_mul_cancel₀ h] at he
  change ‖spatial x‖ ≤ _
  linarith

theorem strict_pair {x p : E4} (hx : x ∈ inside) (hp : p ∈ cone) (hn : p ≠ 0) : 0 < inner ℝ x p := by
  rw [pairing]
  have he : 0 < time p := (cone_self p).mp hp |>.1.lt_of_ne (by
    intro h; apply hn; apply ext_by
    · rw [rest_zero]; exact norm_eq_zero.mp (le_antisymm (h ▸ hp) (norm_nonneg _))
    rw [clock_zero]; exact h.symm)
  have hh := calc ‖spatial x‖ * ‖spatial p‖
                  _ ≤ ‖spatial x‖ * time p := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
                  _ < time x * time p := (mul_lt_mul_of_pos_right hx he)
  have hm := (abs_le.mp (abs_real_inner_le_norm (spatial x) (spatial p))).1
  linarith
end YM.Mink
