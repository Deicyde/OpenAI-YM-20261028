import YM.Push.LOCAL_SPLITTING.Projection

/-! A pre-side triangular leading price in the graded reference coordinates.
No assumption of positivity/bounded inversion of the full reset. This is
linear algebra, not the Wilson calculation of these leading columns or of
their errors; used below to state pre-conversion sufficient step estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels Next.Foundations Work.G08
open scoped BigOperators
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}

def column (F : Labels.Frame G d) (i : F.Index) : F.Coeff := Pi.single i 1

def triangularPrice (F : Labels.Frame G d) (c : ℝ) := ((F.extra+1:ℕ):ℝ) * (c+(F.extra+1:ℕ)*c^2)^(d+1)

/-- No smallness or phase criterion here.

Unit column explicit. -/
structure Leading (B : F.Coeff →ₗ[ℂ] F.Coeff) (c : ℝ) : Prop where
  price : 1 ≤ c
  cap (i j : F.Index) : ‖B (column F j) i‖ ≤ c
  diagonal (i : F.Index) : 1 ≤ c * ‖B (column F i) i‖
  triangular (i j : F.Index) (hN : j ≠ i) : B (column F j) i ≠ 0 → (F.grades j).1 < (F.grades i).1
  unit : B F.e0 = F.e0

variable {B : F.Coeff →ₗ[ℂ] F.Coeff} {c : ℝ}

theorem basis_coeff (v : F.Coeff) : (∑ j : F.Index, v j • column F j) = v := by
  classical
  ext i; simp [column,Finset.sum_apply,Pi.single_apply]

theorem matrix_coeff (B : F.Coeff →ₗ[ℂ] F.Coeff) (v : F.Coeff) (i : F.Index) :
    (∑ j : F.Index, B (column F j) i * v j) = B v i := by
  nth_rw 2 [← basis_coeff v]; simp only [map_sum,Finset.sum_apply,map_smul,Pi.smul_apply, smul_eq_mul,mul_comm]

theorem Leading.cost (h : Leading B c) (v : F.Coeff) :
    F.coeffSize (B v) ≤ triangularPrice F c * F.coeffSize v ∧ F.coeffSize v ≤ triangularPrice F c * F.coeffSize (B v) := by
  classical
  let n := (F.extra+1:ℕ)
  let K : ℝ := c + n*c^2
  have hc := h.price; have hc' := zero_le_one.trans hc
  have hk : c ≤ K := le_add_of_nonneg_right (by positivity)
  have h₁ : 1 ≤ K := hc.trans hk
  have hy := size_nonneg F (B v)
  have he {x : F.Coeff} (a : ℝ) (ha : ∀ i, ‖x i‖ ≤ a) : F.coeffSize x ≤ (n:ℝ)*a := by
    simpa [Frame.coeffSize,n] using Finset.sum_le_sum (s:=Finset.univ) fun i _ => ha i
  constructor
  · apply le_trans (he (c*F.coeffSize v) ?_)
    · unfold triangularPrice; change n*(c*F.coeffSize v) ≤ n*K^(d+1)*F.coeffSize v
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hk.trans (by simpa using pow_le_pow_right₀ h₁ (Nat.le_add_left 1 d))) (size_nonneg F _)) (by positivity)
    intro i; rw [← matrix_coeff B v,Frame.coeffSize, Finset.mul_sum]
    exact (norm_sum_le ..).trans (Finset.sum_le_sum fun j _ => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h.cap i j) (norm_nonneg _))
  have hs (a : ℕ) : ∀ i, (F.grades i).1 < a → ‖v i‖ ≤ K^a*F.coeffSize (B v) := by
    induction a with
    | zero => simp
    | succ a ih =>
      intro i hi
      have hw j (hj : j ≠ i) : ‖B (column F j) i * v j‖ ≤ c * (K^a * F.coeffSize (B v)) := by
        by_cases h' : B (column F j) i = 0
        · rw [h',zero_mul,norm_zero]; positivity
        have ht := h.triangular i j hj h'
        exact (norm_mul_le ..).trans (mul_le_mul (h.cap i j) (ih j (by omega)) (norm_nonneg _) hc')
      let q := Finset.univ.erase i
      have hx : ‖∑ j∈q,B (column F j) i*v j‖ ≤ (n:ℝ)*(c*(K^a*F.coeffSize (B v))) := by
        apply (norm_sum_le ..).trans ((Finset.sum_le_sum (fun j hj => hw j (Finset.ne_of_mem_erase hj))).trans ?_)
        simp only [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.card_le_card (s:=q) (Finset.erase_subset _ _)).trans_eq (show Finset.univ.card = n from Fintype.card_fin _)) (by positivity)
      have hdiag := h.diagonal i
      have hn := show ‖v i‖ ≤ c*‖B (column F i) i*v i‖ from by rw [norm_mul,← mul_assoc]; exact le_mul_of_one_le_left (norm_nonneg _) hdiag
      have H : B (column F i) i*v i = B v i - ∑ j∈q,B (column F j) i*v j := by rw [eq_sub_iff_add_eq, ← matrix_coeff B v i]; exact Finset.add_sum_erase _ (fun j => B (column F j) i*v j) (Finset.mem_univ i)
      apply le_trans hn; rw [H]; apply le_trans (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add ((norm_le_pi_norm ..).trans (norm_le_size ..)) hx)) hc')
      apply le_trans (mul_le_mul_of_nonneg_left (add_le_add_left (le_mul_of_one_le_left hy (one_le_pow₀ (n:=a) h₁)) _) hc'); rw [pow_succ]; unfold K; exact le_of_eq (by ring)
  exact (he _ (fun i => hs (d+1) i (Nat.lt_succ_of_le (F.bound i)))).trans_eq ((mul_assoc ..).symm)

theorem Leading.bijective (h : Leading B c) : Bijective B := by
  have hi := LinearMap.ker_eq_bot.mp ((LinearMap.ker_eq_bot' (f:=B)).mpr fun v hv => size_separates F v (by simpa [hv,Frame.coeffSize] using (h.cost v).2))
  exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩

theorem Leading.core (h : Leading B c) (v : F.Coeff) : F.core (B v) = B (F.core v) := by
  have hzero : B (F.core v) 0 = 0 := by
    rw [← matrix_coeff]; refine Finset.sum_eq_zero fun i _ => ?_
    rcases eq_or_ne i 0 with he|he
    · rw [he,show F.core v 0 = 0 by simp [Frame.core], mul_zero]
    have ht := h.triangular 0 i he
    rw [F.zero_degree] at ht; simp_all
  rw [show B v = v 0 • F.e0 + B (F.core v) from Eq.trans (congr_arg B (core_split F v)) (by rw [map_add,map_smul,h.unit])]
  funext i; by_cases hi : i=0 <;> simp [Frame.core,Frame.e0,Function.update,hi]
  exact hzero.symm
end YM.Push.Local
