import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Wisps



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
The ambient stencil space for this proof consists of sites in one
coarse torus, including a chosen center for every link or row. See
Windows for how dealing (only a bounded shift) with link *windows*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Schur
open Function Filter Lattice RG Wilson Finset Pressure Precision Exterior Tree Matrix Gaussian Rows Wisps 
open scoped Topology BigOperators Classical

variable {c : Side} {α β δ : Type} [Fintype α] [Fintype β] [Fintype δ]

/-- Counting rows/columns, with exponential true geometric rate. -/
structure Pours (L : Matrix α β ℝ) (p : α → Site c) (q : β → Site c) (v C : ℝ) : Prop where
  pos : 0 ≤ C
  row i : ∑ j, rate v (separation (p i) (q j)) * |L i j| ≤ C
  col j : ∑ i, rate v (separation (p i) (q j)) * |L i j| ≤ C

lemma rate_mix (a b : ℝ) (n : ℕ) : rate (a+b) n = rate a n * rate b n := by unfold rate; rw [add_mul,Real.exp_add]

lemma pure {σ C E D : ℝ} (hσ : 0 < σ) (h : 0≤C) {L : Matrix α β ℝ} {p : α → Site c} {q : β → Site c}
    (ht : ∀ i j, rate σ (separation (p i) (q j)) * |L i j| ≤ C)
    (he : ∀ i : Site c, ∑ j, rate (- (σ/2)) (separation i (p j)) ≤ E)
    (hd : ∀ i : Site c, ∑ j, rate (- (σ/2)) (separation i (q j)) ≤ D) :
    Pours L p q (σ/2) ((max E D)*C) := by
  have hi := ((sum_nonneg (s:=univ) (f:=fun j => rate (- (σ/2)) (separation 0 (p j))) fun _ _ => (rate_pos ..).le).trans (he 0)).trans (le_max_left E D)
  have hp i j : rate (σ/2) (separation (p i) (q j)) * |L i j| ≤ rate (-(σ/2)) (separation (p i) (q j)) * C := by
    nth_rw 1 [show σ/2=-(σ/2)+σ by ring, rate_mix,mul_assoc]
    exact mul_le_mul_of_nonneg_left (ht ..) (rate_pos ..).le
  refine ⟨mul_nonneg hi h,fun i => (sum_le_sum fun j _ => hp i j).trans ?_,fun j => (sum_le_sum fun i _ => hp i j).trans ?_⟩
  · rw [← sum_mul]; exact mul_le_mul_of_nonneg_right ((hd _).trans (le_max_right ..)) h
  rw [← sum_mul]; simp_rw [separation_comm _ (q _)]
  exact mul_le_mul_of_nonneg_right ((he _).trans (le_max_left ..)) h

namespace Pours
variable {L : Matrix α β ℝ} {p : α → Site c} {q : β → Site c} {v C D : ℝ}
lemma weaker (h : Pours L p q v C) {t : ℝ} (ht : t ≤ v) {e : ℝ} (he : C ≤ e) : Pours L p q t e := by
  have hi i j : rate t (separation (p i) (q j)) ≤ rate v (separation (p i) (q j)) := by unfold rate; gcongr
  have hp i j := mul_le_mul_of_nonneg_right (hi i j) (abs_nonneg (L i j))
  exact ⟨h.pos.trans he, fun i => (sum_le_sum fun j _ => hp i j).trans ((h.row i).trans he),
    fun j => (sum_le_sum fun i _ => hp i j).trans ((h.col j).trans he)⟩
lemma turn (h : Pours L p q v C) : Pours L.transpose q p v C := by
  have he i j : rate v (separation (q i) (p j)) * |Lᵀ i j| = rate v (separation (p j) (q i)) * |L j i| := by rw [separation_comm]; rfl
  constructor
  · exact h.pos
  · intro i; simp_rw [he]; exact h.col i
  intro j; simp_rw [he]; exact h.row j

lemma fuse (h : Pours L p q v C) {M : Matrix β δ ℝ} {r : δ → Site c}
    (H : Pours M q r v D) (hv : 0 ≤ v) : Pours (L*M) p r v (C*D) := by
  let X i k := rate v (separation (p i) (q k)) * |L i k|
  let Y k j := rate v (separation (q k) (r j)) * |M k j|
  have hp i k : 0 ≤ X i k := mul_nonneg (rate_pos ..).le (abs_nonneg _)
  have ht k j : 0 ≤ Y k j := mul_nonneg (rate_pos ..).le (abs_nonneg _)
  have he i j : rate v (separation (p i) (r j))*|(L*M) i j| ≤ ∑ k, X i k * Y k j := by
    apply le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (rate_pos ..).le)
    rw [mul_sum]; refine sum_le_sum fun k _ => ?_
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_right (rate_le hv (separation_triangle (p i) (q k) (r j))) (by positivity : 0 ≤ |L i k| *|M k j|)).trans_eq
    rw [rate_add]; unfold X Y; ring
  refine ⟨mul_nonneg h.pos H.pos, fun i => (sum_le_sum fun j _ => he i j).trans ?_,fun j => (sum_le_sum fun i _ => he i j).trans ?_⟩
  · rw [sum_comm]; simp_rw [← mul_sum]
    apply le_trans (sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (H.row k) (hp i k))
    rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (h.row _) H.pos
  rw [sum_comm]; simp_rw [← sum_mul]
  apply le_trans (sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h.col k) (ht k j))
  rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (H.col _) h.pos

/-- Drop coordinates, keeping the price. -/
lemma redact (h : Pours L p q v C) (s : Set α) (t : Set β) :
    Pours (L.submatrix ((↑) : s → α) ((↑) : t→β)) (fun i => p i.val) (fun i => q i.val) v C := by
  have hi {E : Type} (W : Set E) [Fintype W] [Fintype E] (u : E → ℝ) (hu : ∀ i, 0 ≤ u i) : (∑ i : W, u i) ≤ ∑ i : E, u i := by
    rw [← sum_image (g:=((↑):W→E)) (f:=u) Subtype.val_injective.injOn]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => hu i
  refine ⟨h.pos,fun i => le_trans ?_ (h.row i),fun j => le_trans ?_ (h.col j)⟩
  · change (∑ j : t, rate v (separation (p i.val) (q j.val)) * |L i.val j.val|) ≤ _
    exact hi _ (fun j => rate _ (separation (p i.val) (q j))*|L i.val j|) (fun _ => mul_nonneg (rate_pos ..).le (abs_nonneg _))
  exact hi s (fun i => rate _ (separation (p i) (q j.val))*|L i j.val|) (fun _ => mul_nonneg (rate_pos ..).le (abs_nonneg _))

lemma bind (h : Pours L p q v C) {R : Matrix α β ℝ} (ht : Pours R p q v D) : Pours (L+R) p q v (C+D) := by
  have he (i j) : rate v (separation (p i) (q j))*|(L+R) i j| ≤ rate v (separation (p i) (q j))*|L i j|+
      rate v (separation (p i) (q j))*|R i j| := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (abs_add_le ..) (rate_pos ..).le
  refine ⟨add_nonneg h.pos ht.pos,fun i => (sum_le_sum (fun j _ => he i j)).trans ?_,fun j => (sum_le_sum (fun i _ => he i j)).trans ?_⟩
  · rw [sum_add_distrib]; exact add_le_add (h.row _) (ht.row _)
  rw [sum_add_distrib]; exact add_le_add (h.col _) (ht.col _)

lemma scale (h : Pours L p q v C) (a : ℝ) : Pours (a • L) p q v (|a| * C) := by
  have he (i j) : rate v (separation (p i) (q j))*|(a • L) i j| = |a| *(rate v (separation (p i) (q j))*|L i j|) := by
    change _*|a*L i j| = _; rw [abs_mul]; ring
  refine ⟨mul_nonneg (abs_nonneg _) h.pos,fun i => ?_,fun j => ?_⟩
  · simp_rw [he,← mul_sum]; exact mul_le_mul_of_nonneg_left (h.row _) (abs_nonneg _)
  simp_rw [he,← mul_sum]; exact mul_le_mul_of_nonneg_left (h.col _) (abs_nonneg _)
end Pours

def sumSq (a : Vec α) := ∑ i, (a i)^2
lemma sumSq_nn (a : Vec α) : 0 ≤ sumSq a := sum_nonneg fun i _ => sq_nonneg _
lemma sumSq_dot (a : Vec α) : sumSq a = a ⬝ᵥ a := by simp [sumSq,sq,dotProduct]

def Gapped (L : Gaussian.Table α) (η : ℝ) := ∀ a : Vec α, η*sumSq a ≤ a ⬝ᵥ (L *ᵥ a)

lemma estimate {L : Matrix α β ℝ} {p : α → Site c} {q : β → Site c} {C : ℝ}
    (h : Pours L p q 0 C) (a : Vec α) (b : Vec β) :
    |a ⬝ᵥ (L *ᵥ b)| ≤ C*(sumSq a + sumSq b)/2 := by
  have hp i (j : β) : |a i * (L i j * b j)| ≤ |L i j| *((a i)^2+(b j)^2)/2 := by
    rw [abs_mul, abs_mul]
    have he := sq_nonneg (|a i|-|b j|)
    have ha : |a i|^2=(a i)^2 := sq_abs _
    have hb : |b j|^2=(b j)^2 := sq_abs _
    have hh : |a i| * |b j| ≤ ((a i)^2+(b j)^2)/2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (L i j))]
  have hr i := h.row i; have hc i := h.col i
  simp_rw [rate,zero_mul,Real.exp_zero,one_mul] at hr hc
  unfold dotProduct mulVec; simp_rw [dotProduct, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g:=fun i => ∑ j, |L i j| *((a i)^2+(b j)^2)/2) (fun i _ =>
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => hp i j))).trans ?_)
  simp_rw [← sum_div,mul_add,sum_add_distrib,← sum_mul]
  rw [show ∑ i, ∑ j, |L i j| * b j ^ 2 = ∑ j, (∑ i, |L i j|)*b j ^ 2 from ?_]
  swap
  · rw [sum_comm]; simp_rw [← sum_mul]
  unfold sumSq; rw [Finset.mul_sum,Finset.mul_sum]
  gcongr
  all_goals first | exact hr _ | exact hc _
end YM.Next.SectorChange.Schur
