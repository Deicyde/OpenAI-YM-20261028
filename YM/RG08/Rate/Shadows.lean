import YM.RG08.Rate.Stair

/-!
# Paying for skipped last factors and adjacent step data
-/
noncomputable section
namespace YM.RG08.Rate.Stair
open Real
open Finset

set_option autoImplicit false
universe v

variable {X : Type v} {W : Stair X} (x : X) (i : ℕ)

/-- Take a quotation from one level finer. Zero past top so only valid inputs are needed. -/
def nextUp (W : Stair X) (f : Stair.Array X) : Stair.Array X :=
  fun x i => if i < W.top x then f x (i+1) else 0

def stepOnly (W : Stair X) (f : Stair.Array X) : Stair.Array X :=
  fun x i => if i < W.top x then f x i else 0

theorem finer {x : X} {i : ℕ} (hx : W.Here x i) (hi : i < W.top x) : W.Here x (i+1) := ⟨hx.1.trans (by omega), hi⟩

variable {f g : Stair.Array X}

theorem Poly.stepOnly (h : W.Poly f) : W.Poly (W.stepOnly f) :=
  h.mono fun x i hi=> by
    unfold Stair.stepOnly
    split <;> simp [h.nonneg (x:=x) (i:=i) hi]

theorem Fade.stepOnly (h : W.Fade f) : W.Fade (W.stepOnly f) :=
  h.mono fun x i hi=> by
    unfold Stair.stepOnly
    split <;> simp [h.nonneg (x:=x) (i:=i) hi]

theorem Poly.hereAge (W : Stair X) : W.Poly W.age :=
  ⟨1,1,zero_le_one,fun x i _=> ⟨(W.age_big x i).trans' (by norm_num),by simp⟩⟩

def Admits (W : Stair X) := W.Poly (W.stepOnly W.length)

theorem Admits.ages (h : W.Admits) : W.Poly (W.nextUp W.age) := by
  have hN : W.Poly (W.stepOnly W.length) := h
  refine ((Poly.hereAge W).add hN).mono fun x i hi=> ?_
  dsimp [Stair.stepOnly,nextUp]
  split
  · have he:= W.age_later x i (i+1) (by omega)
    rw [time_step, add_sub_cancel_left] at he
    exact ⟨(W.age_big ..).trans' (by norm_num), he.trans (by
      have hp : 0 < W.length x i := (W.length_large x i).trans_lt' (by norm_num)
      linarith only [Real.log_le_sub_one_of_pos hp])⟩
  simp only [le_refl,true_and,add_zero]; exact (W.age_big ..).trans' (by norm_num)

theorem Poly.finer (h : W.Poly f) (ha : W.Admits) : W.Poly (W.nextUp f) := by
  obtain ⟨A,d,hA,H⟩:=h
  refine ((Poly.constant W hA).mul (ha.ages.pow d)).mono fun x i hi=>?_
  dsimp [nextUp]
  split
  · rename_i he; exact H _ _ (Stair.finer hi he)
  exact ⟨le_rfl,mul_nonneg hA (pow_nonneg (by norm_num) _)⟩

theorem Admits.power (h : W.Admits) (c : ℝ) : W.Poly (W.stepOnly fun x i=> W.length x i ^ c) := by
  obtain ⟨n,hn⟩:= exists_nat_gt c
  refine (Poly.pow h n).mono fun x i hi=> ?_
  dsimp [stepOnly]
  split
  · have hx : 1 ≤ W.length x i := le_trans (by norm_num) (W.length_large x i)
    have he : 0 ≤ W.length x i := zero_le_one.trans hx
    exact ⟨Real.rpow_nonneg he _, (Real.rpow_le_rpow_of_exponent_le hx hn.le).trans_eq (by simp)⟩
  exact ⟨le_rfl,pow_nonneg (by norm_num) _⟩

theorem Fade.finer (h : W.Fade f) (ha : W.Admits) : W.Fade (W.nextUp f) := by
  obtain ⟨θ,hθ,ht⟩:=h
  refine ⟨θ,hθ,?_⟩
  have hh:= (ht.finer ha).mul (ha.power θ)
  convert hh using 1
  funext x i
  dsimp [Stair.stepOnly,nextUp]
  rw [weight_length]
  split <;> ring

/-- A cost concentrated at the fine top needs no better UV defect than its bulk bound. -/
theorem Fade.of_top (h : W.Poly f) (hg : ∀ x i, W.Here x i → i < W.top x → f x i = 0) : W.Fade f := by
  refine ⟨1,zero_lt_one,h.mono fun x i hi=>?_⟩
  by_cases e : i = W.top x
  · subst i; simpa [weight] using h.nonneg hi
  simp [hg x i hi (lt_of_le_of_ne hi.2 e)]

/-- Export in the `kpin` convention. -/
theorem Fade.cap (h : W.Fade f) : ∃ (A : ℝ) (d : ℕ) (c : ℝ), 0 ≤ A ∧ 0 < c ∧
   ∀ x i, W.Here x i → 0 ≤ f x i ∧
     f x i ≤ A * W.age x i^d * (((W.sched x).a (W.top x) / (W.sched x).a i)^c) := by
  have hh : ∀ x i, W.Here x i → 0 ≤ f x i := fun _ _ hi=> h.nonneg hi
  obtain ⟨c,hc,A,d,hA,Hu⟩:=h
  exact ⟨A,d,c,hA,hc,fun x i hi=> ⟨hh x i hi, by
    rw [← W.weight_inv, ← div_eq_mul_inv]
    exact (le_div_iff₀ (W.weight_pos ..)).mpr (Hu x i hi).2⟩⟩

theorem Fade.acquire {A c : ℝ} {d : ℕ} (h : 0 ≤ A) (hc : 0 < c)
    (hf : ∀ x i, W.Here x i → 0 ≤ f x i ∧
      f x i ≤ A * W.age x i^d * (((W.sched x).a (W.top x) / (W.sched x).a i)^c)) : W.Fade f := by
  refine ⟨c,hc,A,d,h,fun x i hi=> ?_⟩
  obtain ⟨he,hA⟩:= hf x i hi
  rw [← W.weight_inv, ← div_eq_mul_inv] at hA
  exact ⟨mul_nonneg he (W.weight_pos ..).le,(le_div_iff₀ (W.weight_pos ..)).mp hA⟩

end YM.RG08.Rate.Stair
