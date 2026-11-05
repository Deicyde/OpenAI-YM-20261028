import YM.Labels.Basis

/-! Reference vs polynomial labels.
Coordinate spaces use sup top/norm by default; size in estimate below is ℓ¹.
The weighted diagonal commuting with O(4) is an actual identity. Do not
identify O(4) action after the physical all-spectator quotient by simply
descending the whole of the polynomial one. -/

set_option autoImplicit false
noncomputable section
namespace YM.Labels.Frame
open Function Set
open scoped Topology BigOperators

variable {G : Gauge} {d : ℕ} (F : Frame G d)

abbrev Index := Fin (F.extra+1)
abbrev Coeff := F.Index → ℂ

def coords : Label G d ≃ₗ[ℂ] F.Coeff := F.basis.equivFun

@[simp] theorem coords_basis (i : F.Index) : F.coords (F.basis i) = Pi.single i 1 := by
  ext1 j
  change F.basis.repr (F.basis i) j = _
  rw [Module.Basis.repr_self]
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

def e0 : F.Coeff := Pi.single 0 1
@[simp] theorem coords_unit : F.coords (unit G d) = F.e0 := F.starts_unit ▸ F.coords_basis 0

theorem power_coefficient (i : F.Index) {v : Label G d} {m} (h : m ≠ F.grades i) (hv : v ∈ Grade m) :
    F.coords v i = 0 := by
  let B := F.basis
  have ha : gradePart m v = v := gradePart_self v m hv
  have hx : v = ∑ j : F.Index, gradePart m (B.repr v j • B j) := calc
    v = gradePart m v := ha.symm
    _ = gradePart m (∑ j : F.Index, B.repr v j • B j) := congr_arg _ (B.sum_repr _).symm
    _ = _ := map_sum ..
  have hz (j : F.Index) : F.coords (gradePart m (B.repr v j • B j)) i = 0 := by
    rcases eq_or_ne (F.grades j) m with he|he
    · rw [map_smul, ← he, gradePart_self (F.basis j) _ (F.pure j), map_smul, F.coords_basis j,
        Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
      exact fun w ↦ h (w ▸ he.symm)
    · rw [map_smul, gradePart_zero (F.basis j) m _ he.symm (F.pure j)]; simp
  conv_lhs => rw [hx]
  rw [map_sum, Finset.sum_apply]; simp_rw [hz]; exact Finset.sum_const_zero

theorem zero_degree : F.grades 0 = (0,0) := by
  refine pure_unique (u := unit G d) unit_not_zero _ _ ?_ (unit_grade _)
  rw [← F.starts_unit]; exact F.pure _

theorem factors_pos (i : F.Index) (hi : i ≠ 0) : 0 < (F.grades i).2 := by
  by_contra! hy
  obtain ⟨k,hk⟩ := scalar_grade (v := F.basis i) (F.grades i).1 (by rw [← Nat.eq_zero_of_le_zero hy]; exact F.pure _)
  have h : F.coords (F.basis i) i = 0 := by rw [hk, map_smul, F.coords_unit]; simp [e0,Pi.single_eq_of_ne hi]
  rw [coords_basis] at h; simp at h

def scaled (t : ℝ) : F.Coeff →ₗ[ℂ] F.Coeff where
  toFun x j := ((t^(F.grades j).2 : ℝ) : ℂ) * x j
  map_add' x y := by ext1; simp [mul_add]
  map_smul' z x := by ext1; simp; ring

@[simp] theorem scaled_apply (t : ℝ) (x : F.Coeff) (i : F.Index) :
    F.scaled t x i = ((t^(F.grades i).2 : ℝ) : ℂ) * x i := rfl

@[simp] theorem scaled_inv {t : ℝ} (h : t ≠ 0) (x : F.Coeff) : F.scaled t (F.scaled t⁻¹ x) = x := by
  funext i
  simp only [scaled_apply, inv_pow, Complex.ofReal_inv, ← mul_assoc,
    mul_inv_cancel₀ (show ((t ^ (F.grades i).2 : ℝ) : ℂ) ≠ 0 by exact_mod_cast pow_ne_zero _ h), one_mul]

theorem scaled_pure (t : ℝ) (m : ℕ × ℕ) {x : Label G d} (h : x ∈ Grade m) :
    F.scaled t (F.coords x) = ((t^m.2 : ℝ) : ℂ) • F.coords x := by
  funext i
  by_cases he : m = F.grades i
  · rw [he]; rfl
  simp [F.power_coefficient i he h]

@[simp] theorem scaled_unit (t : ℝ) : F.scaled t F.e0 = F.e0 := by
  rw [← F.coords_unit, F.scaled_pure t (0,0) (unit_grade d)]; simp

/-- Real unrenormalized orthogonal action on reference labels. After
renormalization only H (signed-permutation) is supplied automatically. -/
def act (s : Ortho) : F.Coeff →ₗ[ℂ] F.Coeff :=
  F.coords.toLinearMap.comp ((tensor s).comp F.coords.symm.toLinearMap)

@[simp] theorem act_coords (s : Ortho) (x : Label G d) : F.act s (F.coords x) = F.coords (tensor s x) := by
  simp [act]

@[simp] theorem act_mul (u v : Ortho) (x : F.Coeff) : F.act (u*v) x = F.act u (F.act v x) := by
  obtain ⟨x,rfl⟩ := F.coords.surjective x
  simp
@[simp] theorem act_one (x : F.Coeff) : F.act 1 x = x := by
  obtain ⟨x,rfl⟩ := F.coords.surjective x
  simp

theorem scaling (t : ℝ) (s : Ortho) (c : F.Coeff) :
    F.scaled t (F.act s c) = F.act s (F.scaled t c) := by
  have H : (F.scaled t ∘ₗ F.act s ∘ₗ F.coords.toLinearMap) =
      (F.act s ∘ₗ F.scaled t ∘ₗ F.coords.toLinearMap) := by
    refine F.basis.ext fun i ↦ ?_
    let B := F.basis i
    have h := F.pure i
    have e : tensor s B ∈ Grade (F.grades i) := by
      have hv := gradePart_mem (F.grades i) (tensor s B)
      rw [gradePart_turn, gradePart_self B _ h] at hv; exact hv
    change F.scaled t (F.act s (F.coords B)) = F.act s (F.scaled t (F.coords B))
    rw [act_coords, F.scaled_pure t _ e, F.scaled_pure t _ (show B ∈ _ from h), map_smul, act_coords]
  obtain ⟨x,rfl⟩ := F.coords.surjective c
  exact LinearMap.congr_fun H x

theorem conj_basis (v : F.Coeff) (i : F.Index) : F.coords (realBar (F.coords.symm v)) i = star (v i) := by
  let f := F.coords.symm v
  change F.coords (realBar f) i = _
  have e : realBar f = ∑ j, star (F.basis.repr f j) • F.basis j := calc
    _ = realBar (∑ j, F.basis.repr f j • F.basis j) := congr_arg _ (F.basis.sum_repr f).symm
    _ = _ := by rw [_root_.map_sum]; simp [F.realForm]
  rw [e, map_sum, Finset.sum_apply]
  simp_rw [map_smul, coords_basis, Pi.smul_apply]
  simp only [Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  change star (F.coords f i) = _; simp [f]

def core : F.Coeff →ₗ[ℂ] F.Coeff where
  toFun v := Function.update v 0 0
  map_add' x y := by funext i; by_cases hi : i = 0 <;> simp [Function.update,hi]
  map_smul' a x := by funext i; by_cases hi : i = 0 <;> simp [Function.update,hi]

def coeffSize (x : F.Coeff) : ℝ := ∑ i, ‖x i‖
end YM.Labels.Frame
