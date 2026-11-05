import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Census
import YM.Next.FREE_KERNELS.Lifts
import YM.Progress.STATIONARY_SCENES.Green

/-!
# Matrix prices (counting, true distances)

Common post-L inverse script for `along`-type weight functions. `(I+uS)` or
`A_s` interpolation later. No series positivity assumed for a window.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Control
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] {c : Side} {a : ι → Site c} {b : κ → Site c}
variable {A B : Matrix ι ι ℝ} {M : Matrix ι κ ℝ} {r η X Y : ℝ}

abbrev Price (a : ι → Site c) (b : κ → Site c) (M : Matrix ι κ ℝ) (r X : ℝ) := Both a b M r X X

omit [Fintype ι] in
lemma pricing (h : Rows a b M r X) (e : η ≤ r) (g : X ≤ Y) : Rows a b M η Y := by
  intro i; apply le_trans _ ((h i).trans g)
  refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  exact Real.exp_monotone (mul_le_mul_of_nonneg_right e (Nat.cast_nonneg _))
lemma increase (h : Price a b M r X) (e : η ≤ r) (g : X ≤ Y) : Price a b M η Y :=
    ⟨pricing h.1 e g, pricing h.2 e g⟩
omit [Fintype ι] in
lemma trace0 (h : Rows a b M r X) (i : ι) (j : κ) : wt r (a i) (b j)*|M i j| ≤ X :=
  le_trans (Finset.single_le_sum (f := fun j => wt r (a i) (b j)*|M i j|)
    (fun _ _ => mul_nonneg (wt_pos ..).le (abs_nonneg _)) (mem_univ _)) (h i)
omit [Fintype ι] in
lemma only_price (h : Rows a b M r X) (he : 0≤r) (i : ι) (j : κ) : |M i j| ≤ X := by
  simpa only [wt,zero_mul,Real.exp_zero, one_mul] using! trace0 (pricing h he le_rfl) i j
omit [Fintype ι] in
lemma pure_pay (h : Rows a b M r X) (he : 0≤r) (i : ι) : ∑ j, |M i j| ≤ X := by
  simpa only [wt,zero_mul,Real.exp_zero,one_mul] using pricing h he le_rfl i
lemma density (a : ι → Site c) (A : Matrix ι ι ℝ) (r : ℝ) (h : IsHermitian A) {X : ℝ} (he : Rows a a A r X) : Price a a A r X := by
  refine ⟨he,?_⟩; rw [← show Aᴴ=A.transpose from by ext; simp,h.eq]; exact he

lemma paid_add (h : Price a a A r X) (k : Price a a B r Y) : Price a a (A+B) r (X+Y) := by
  refine ⟨h.1.plus k.1,?_⟩; rw [transpose_add]; exact h.2.plus k.2
lemma paid_mul {g : ν → Site c} [Fintype ν] {L : Matrix κ ν ℝ} (h : Price a b M r X) (k : Price b g L r Y)
    (he : 0 ≤ r) (hh : 0 ≤ X) (hf : 0 ≤ Y) : Price a g (M*L) r (X*Y) := by
  refine ⟨h.1.multiply he k.1 hf,?_⟩; rw [transpose_mul, mul_comm X Y]
  exact k.2.multiply he h.2 hh
lemma flipped (h : Price a b M r X) : Price b a M.transpose r X := ⟨h.2,by rw [transpose_transpose]; exact h.1⟩
lemma weighted_by (h : Price a b M r X) (t : ℝ) : Price a b (t • M) r (|t| *X) := by
  refine ⟨h.1.pay t,?_⟩; rw [transpose_smul]; exact h.2.pay t
lemma spent_neg (h : Price a b M r X) : Price a b (-M) r X := by
  simpa only [neg_smul,one_smul, abs_neg,abs_one,one_mul] using weighted_by h (-1)

lemma one_pay [DecidableEq ι] (a : ι→ Site c) (r : ℝ) : Price a a (1:Matrix ι ι ℝ) r 1 := by
  refine density _ _ _ Matrix.isHermitian_one fun i => ?_; rw [Finset.sum_eq_single i]
  · simp [wt]
  · intro j _ hj; simp [hj.symm]
  simp
lemma nn (v : ι → ℝ) : 0 ≤ dotProduct v v := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
lemma top (h : Price a a A r X) (he : 0≤r) (v : ι→ℝ) : |dotProduct v (A *ᵥ v)| ≤ X*dotProduct v v := by
  exact Green.schur A v X (pure_pay h.1 he) (fun j => pure_pay h.2 he j)
lemma bilinear_floor (h : Price a a A r X) (he : 0 ≤ r) : Bottom A (-X) := by
  intro v; rw [neg_mul]; exact (abs_le.mp (top h he v)).1
lemma lower_inverse [DecidableEq ι] {ρ : ℝ} (h : Price a a A r X) (he : 0≤r) (hk : 0 < X) (hA : IsHermitian A)
    (hG : Bottom A ρ) (hr : 0 ≤ ρ) (H : A*A⁻¹=1) : Bottom A⁻¹ X⁻¹ := by
  intro v; let w := A⁻¹ *ᵥ v
  have hv : A *ᵥ w=v := by unfold w; rw [Matrix.mulVec_mulVec,H,Matrix.one_mulVec]
  let x := X⁻¹ • v
  have hf : 0 ≤ dotProduct (w-x) (A *ᵥ (w-x)) := (mul_nonneg hr (nn _)).trans (hG (w-x))
  have hg (u v) : dotProduct u (A *ᵥ v)=dotProduct (A *ᵥ u) v := by
    have he : Aᵀ=A := by rw [← show Aᴴ=Aᵀ from by ext; simp,hA.eq]
    conv_lhs => rhs; arg 1; rw [← he]
    rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
  have ht : dotProduct x (A *ᵥ x) ≤ dotProduct x v := by
    apply ((le_abs_self _).trans (top h he x)).trans
    exact le_of_eq (by
      unfold x
      rw [smul_dotProduct,smul_dotProduct,dotProduct_smul]
      change X*(X⁻¹*(X⁻¹*_))=_
      rw [← mul_assoc, mul_inv_cancel₀ hk.ne',one_mul]; rfl)
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
    hv,hg,dotProduct_comm (A *ᵥ w),hv] at hf
  change _ ≤ dotProduct v w
  rw [dotProduct_comm v w]; apply le_trans (b:=dotProduct x v) (by unfold x; rw [smul_dotProduct]; rfl)
    (by linarith only [hf,ht])
lemma definite (he : IsHermitian A) (h : Bottom A X) (hp : 0 < X) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos he; intro v hv
  rw [star_trivial]; apply lt_of_lt_of_le ?_ (h v); exact mul_pos hp (by
    obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by simpa only [Ne,funext_iff,Pi.zero_apply,not_forall] using hv
    exact (mul_self_pos.mpr hi).trans_le (Finset.single_le_sum (f:=fun j=>v j*v j)
      (fun j _ => mul_self_nonneg _) (mem_univ _)))

omit [Fintype ι] in
lemma neighbor_pay (h : Rows a b M r X) (n : ℕ) (H : ∀ i j, separation (a i) (b j) ≤ n → M i j=0) (he : η ≤ r) :
    Rows a b M η (Real.exp ((η-r)*n)*X) := by
  intro i
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (h i) (Real.exp_pos _).le); rw [mul_sum]
  apply sum_le_sum; intro j hj
  by_cases ht : separation (a i) (b j) ≤ n
  · simp [H i j ht]
  rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _); unfold wt; rw [← Real.exp_add]
  apply Real.exp_monotone
  have hh : (n:ℝ) ≤ (separation (a i) (b j):ℝ) := by exact_mod_cast (le_of_lt (lt_of_not_ge ht))
  nlinarith
lemma spend_far (h : Price a b M r X) (n : ℕ) (H : ∀ i j, separation (a i) (b j) ≤ n → M i j=0) (he : η ≤ r) :
    Price a b M η (Real.exp ((η-r)*n)*X) :=
  ⟨neighbor_pay h.1 n H he, neighbor_pay h.2 n (fun i j hij => H j i ((separation_comm ..) ▸ hij)) he⟩
end YM.ConnectedActivityE6.Control
