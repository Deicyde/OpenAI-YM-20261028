import YM.Push.FREE_RESOLVENT.ListJets
import YM.Push.FREE_RESOLVENT.Weights
import YM.Work.B04

/-!
# Polarized Schur tests

Positive marks carried on the row or column coordinate. Use both for ANY
list of requested derivatives. Marks may represent polynomial input growth
*debt* (test directions with a radial polynomial weight around an anchor,
price a derivative by the inverse of that polynomial at a slot). They can
instead price *connectivity/exponential decay* to EACH fixed external
Taylor position. We don't assert those stronger prices from directional
bounds. One can augment the list at use (e.g. pay an extra mark tracing a
local tag change).

The mark displacement cost is explicit and can be used with successive rate
shrinkages. The *zero* derivative order consumed by a weight must still be
paid at every slot; no averaging over sites in these conventions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open TestD Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {τ X ι κ μ : Type*}

/-- Positive mark. Motion controlled when using products. -/
structure Mark (τ X : Type*) where
  cents (t : τ) (x : X) : ℝ
  pos t x : 0 < cents t x

namespace Mark
variable {C : Mark τ X} {D : Cost X}

/-- Absolute distance escalation on moving the origin of a derivative weight.
Exponent δ *per occurrence*. -/
structure Move (C : Mark τ X) (D : Cost X) (δ U : ℝ) : Prop where
  widen t x y : C.cents t x ≤ U * D.weight δ x y * C.cents t y

def pay (C : Mark τ X) : List τ → X → ℝ
  | [], _ => 1
  | b :: l,x => C.cents b x*C.pay l x
lemma pay_pos (C : Mark τ X) (l : List τ) (x : X) : 0 < C.pay l x := by
  induction l with
  | nil => exact zero_lt_one
  | cons b l h => exact mul_pos (C.pos ..) h
lemma pay_masks (C : Mark τ X) (l : List τ) (m : Masks l) (x : X) :
    C.pay l x = C.pay (lo l m) x * C.pay (hi l m) x := by
  induction l with
  | nil => simp [pay,lo,hi]
  | cons b l h => cases m with
    | inl i => rw [lo,hi,pay,pay,h i,mul_assoc]
    | inr i => rw [lo,hi,pay,pay,h i,mul_left_comm (C.cents ..)]
lemma Move.transfer {δ U : ℝ} (h : Move C D δ U) (hu : 0 ≤ U) (l : List τ) (x y : X) :
    C.pay l x ≤ U^l.length*D.weight (l.length*δ) x y*C.pay l y := by
  induction l with
  | nil => simp [pay]
  | cons t l ih =>
    rw [pay]
    refine (mul_le_mul (h.widen t x y) ih (pay_pos ..).le (mul_nonneg (mul_nonneg hu (D.weight_nn ..)) (C.pos ..).le)).trans_eq ?_
    simp only [pay, List.length_cons, pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul, Cost.weight_add]; ring

/-- Nonnegative norm weighting, deliberately on kernel type, not requiring
G to have any uniform sup price. -/
structure Rates [Fintype κ] (C : Mark τ X) (D : Cost X) (a : ι → X) (b : κ → X) (l : List τ) (σ M : ℝ) (A : Matrix ι κ ℝ) : Prop where
  rows (i : ι) : C.pay l (a i) * (∑ j, D.weight σ (a i) (b j)*|A i j|) ≤ M

structure Bill [Fintype ι] [Fintype κ] (C : Mark τ X) (D : Cost X) (a : ι → X) (b : κ → X) (l : List τ) (σ M : ℝ) (A : Matrix ι κ ℝ) : Prop where
  row : Rates C D a b l σ M A
  col : Rates C D b a l σ M A.transpose

variable [Fintype κ]
variable {A B : Matrix ι κ ℝ} {l : List τ} {δ U σ γ R M N : ℝ}
variable {a : ι → X} {b : κ → X} {c : μ → X}
namespace Rates
lemma mono (h : Rates C D a b l σ M A) (hσ : γ ≤ σ) (hm : M ≤ N) : Rates C D a b l γ N A := by
  constructor; intro i; apply le_trans ?_ ((h.rows i).trans hm)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => ?_) (pay_pos ..).le
  exact mul_le_mul_of_nonneg_right (D.weight_mono hσ ..) (abs_nonneg _)
lemma zero (hM : 0 ≤ M) : Rates C D a b l σ M 0 := ⟨fun i => by simpa only [Matrix.zero_apply, abs_zero,
  mul_zero, Finset.sum_const_zero]⟩
lemma abs_le (h : Rates C D a b l σ M A) (hh : ∀ i j, |B i j| ≤ |A i j|) : Rates C D a b l σ M B := by
  constructor; intro i; apply le_trans ?_ (h.rows i)
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hh i j) (D.weight_nn ..)) (C.pay_pos ..).le
lemma add (h : Rates C D a b l σ M A) (ht : Rates C D a b l σ N B) :
    Rates C D a b l σ (M+N) (A+B) := by
  constructor; intro i; apply le_trans ?_ (add_le_add (h.rows i) (ht.rows i))
  rw [← mul_add, ← Finset.sum_add_distrib]; apply mul_le_mul_of_nonneg_left _ (C.pay_pos ..).le
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_add_le ..) (D.weight_nn ..)
lemma neg (h : Rates C D a b l σ M A) : Rates C D a b l σ M (-A) := h.abs_le (by simp)
lemma submatrix {ι' κ' : Type*} (u : ι' → ι) {v : κ' → κ} [Fintype κ']
    (hv : Function.Injective v) (h : Rates C D a b l σ M A) :
    Rates C D (a ∘ u) (b ∘ v) l σ M (A.submatrix u v) := by
  constructor; intro i; refine le_trans ?_ (h.rows (u i))
  apply mul_le_mul_of_nonneg_left _ (C.pay_pos ..).le
  exact Cost.sum_comp_le hv _ (fun j => mul_nonneg (D.weight_nn ..) (abs_nonneg _))
lemma entry (h : Rates C D a b l σ M A) (i j) :
    C.pay l (a i) * (D.weight σ (a i) (b j)*|A i j|) ≤ M := by
  apply le_trans ?_ (h.rows i)
  apply mul_le_mul_of_nonneg_left _ (C.pay_pos ..).le
  exact Finset.single_le_sum (fun j _ => mul_nonneg (D.weight_nn ..) (abs_nonneg _)) (Finset.mem_univ j)
lemma of_entry (hV : D.Volume b (σ-γ) N)
    (hM : 0 ≤ M)
    (h : ∀ i j, C.pay l (a i)*(D.weight σ (a i) (b j)*|A i j|) ≤ M) :
    Rates C D a b l γ (N*M) A := by
  constructor; intro i; apply le_trans ?_ (mul_le_mul_of_nonneg_right (hV.bound (a i)) hM)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  apply le_trans _ (mul_le_mul_of_nonneg_left (h i j) (D.weight_nn (-(σ-γ)) (a i) (b j)))
  apply le_of_eq
  have he : γ=(-(σ-γ))+σ := by ring
  nth_rw 1 [he,Cost.weight_add]; ring
lemma far (hA : Rates C D a b l σ M A) (R : ℝ) (hg : γ ≤ σ)
    (hs : ∀ i j, B i j ≠ 0 → R ≤ D.d (a i) (b j)) (he : ∀ i j, |B i j| ≤ |A i j|) :
    Rates C D a b l γ (Real.exp (-(σ-γ)*R)*M) B := by
  constructor; intro i
  apply le_trans ?_ (mul_le_mul_of_nonneg_left (hA.rows i) (Real.exp_pos _).le)
  rw [mul_left_comm (Real.exp _) (C.pay _ _)]
  apply mul_le_mul_of_nonneg_left _ (C.pay_pos ..).le
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h : B i j=0
  · rw [h, abs_zero,mul_zero]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (D.weight_nn ..) (abs_nonneg _))
  rw [← mul_assoc]; exact mul_le_mul (D.weight_shrink hg (hs i j h)) (he i j) (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le (D.weight_nn ..))

lemma mul [Fintype μ] {B : Matrix κ μ ℝ} {l₁ l₂ : List τ}
    (h : Move C D δ U) (hu : 0 ≤ U) (hc : 0 ≤ γ) (hh : γ+l₂.length*δ ≤ σ)
    (hw : ∀ x, C.pay l x=C.pay l₁ x*C.pay l₂ x) (hp : Rates C D a b l₁ σ M A)
    (hq : Rates C D b c l₂ γ N B) (hn : 0 ≤ N) : Rates C D a c l γ (U^l₂.length*N*M) (A*B) := by
  constructor; intro i
  let x (j) := D.weight σ (a i) (b j) * |A i j|
  let z (j) := D.weight γ (a i) (b j) * |A i j|
  let y (j k) := D.weight γ (b j) (c k) * |B j k|
  have h1 (j : κ) : C.pay l₂ (a i)*z j ≤ U^l₂.length*x j*C.pay l₂ (b j) := calc
    _ ≤ (U^l₂.length*D.weight (l₂.length*δ) (a i) (b j)*C.pay l₂ (b j)) * z j := by
      apply mul_le_mul_of_nonneg_right (h.transfer hu l₂ (a i) (b j)); exact mul_nonneg (D.weight_nn ..) (abs_nonneg _)
    _ = U^l₂.length*(D.weight (γ+l₂.length*δ) (a i) (b j)*|A i j|)*C.pay l₂ (b j) := by
      unfold z; rw [Cost.weight_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (C.pay_pos ..).le
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
      exact mul_le_mul_of_nonneg_right (D.weight_mono hh ..) (abs_nonneg _)
  have h2 (j : κ) : C.pay l₂ (a i)*(∑ k, z j*y j k) ≤ U^l₂.length*N*x j := by
    rw [← Finset.mul_sum, ← mul_assoc]
    have hh := (mul_le_mul_of_nonneg_left (hq.rows j) (show 0 ≤ U^l₂.length*x j from
      mul_nonneg (pow_nonneg hu _) (mul_nonneg (D.weight_nn ..) (abs_nonneg _))))
    calc
      _ ≤ U^l₂.length*x j*C.pay l₂ (b j) * ∑ k, y j k :=
        mul_le_mul_of_nonneg_right (h1 _) (Finset.sum_nonneg (fun k _ => mul_nonneg (D.weight_nn ..) (abs_nonneg (B j k))))
      _ ≤ _ := by rw [mul_assoc (U^l₂.length*x j), mul_right_comm _ N]; exact hh
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => Cost.Rows.term_mul hc a b c A B i k)) (C.pay_pos l (a i)).le) ?_
  change C.pay l (a i)*(∑ k, ∑ j, z j*y j k) ≤ _
  rw [Finset.sum_comm,hw,mul_assoc (C.pay ..), Finset.mul_sum]
  calc
    _ ≤ C.pay l₁ (a i)*∑ j, U^l₂.length*N*x j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h2 j) (C.pay_pos ..).le
    _ ≤ _ := by rw [← Finset.mul_sum,mul_left_comm]; exact mul_le_mul_of_nonneg_left
                  (hp.rows _) (mul_nonneg (pow_nonneg hu _) hn)
end Rates

section both
variable [Fintype ι]
namespace Bill
lemma mono (h : Bill C D a b l σ M A) (hσ : γ ≤ σ) (hm : M ≤ N) : Bill C D a b l γ N A :=
  ⟨h.row.mono hσ hm,h.col.mono hσ hm⟩
lemma zero (hM : 0 ≤ M) : Bill C D a b l σ M 0 := ⟨Rates.zero hM,Rates.zero hM⟩
lemma origin (C : Mark τ X) (h : D.Schur a b σ M A) : Bill C D a b [] σ M A := by
  constructor <;> constructor <;> intro i <;> rw [pay,one_mul]
  · exact h.rows.bound i
  exact h.cols.bound i
lemma reclaim (h : Bill C D a b [] σ M A) : D.Schur a b σ M A := by
  constructor <;> constructor <;> intro i
  · simpa only [pay,one_mul] using h.row.rows i
  simpa only [pay,one_mul] using h.col.rows i
lemma flip (h : Bill C D a b l σ M A) : Bill C D b a l σ M A.transpose := ⟨h.col,h.row⟩
lemma abs_le (h : Bill C D a b l σ M A) (he : ∀ i j, |B i j| ≤ |A i j|) : Bill C D a b l σ M B :=
  ⟨h.row.abs_le he,h.col.abs_le fun i j => he j i⟩
lemma add (h : Bill C D a b l σ M A) (ht : Bill C D a b l σ N B) :
    Bill C D a b l σ (M+N) (A+B) := ⟨h.row.add ht.row,h.col.add ht.col⟩
lemma neg (h : Bill C D a b l σ M A) : Bill C D a b l σ M (-A) := ⟨h.row.neg,h.col.neg⟩
lemma sub (h : Bill C D a b l σ M A) (ht : Bill C D a b l σ N B) :
    Bill C D a b l σ (M+N) (A-B) := by rw [sub_eq_add_neg]; exact h.add ht.neg
lemma submatrix {ι' κ' : Type*} {u : ι' → ι} {v : κ' → κ} [Fintype ι'] [Fintype κ']
    (hu : Function.Injective u) (hv : Function.Injective v) (h : Bill C D a b l σ M A) :
    Bill C D (a ∘ u) (b ∘ v) l σ M (A.submatrix u v) := ⟨h.row.submatrix u hv, h.col.submatrix v hu⟩
lemma far (hA : Bill C D a b l σ M A) (R : ℝ) (hg : γ ≤ σ)
    (hs : ∀ i j, B i j ≠ 0 → R ≤ D.d (a i) (b j)) (he : ∀ i j, |B i j| ≤ |A i j|) :
    Bill C D a b l γ (Real.exp (-(σ-γ)*R)*M) B := ⟨hA.row.far R hg hs he,
      hA.col.far R hg (fun i j h => by rw [D.comm]; exact hs j i h) fun i j => he j i⟩
lemma sum_budget {ρ : Type*} (S : Finset ρ) (w : ρ → ℝ) (T : ρ → Matrix ι κ ℝ) (h : ∀ i ∈ S, Bill C D a b l σ (w i) (T i)) :
    Bill C D a b l σ (∑ i ∈ S, w i) (∑ i ∈ S, T i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact zero le_rfl
  | @insert i S he ih => rw [Finset.sum_insert he, Finset.sum_insert he]; exact (h i (by simp)).add (ih fun i hi => h _ (by simp [hi]))
lemma mul [Fintype μ] {B : Matrix κ μ ℝ} {l₁ l₂ : List τ}
    (h : Move C D δ U) (hn : 0 ≤ δ) (hu : 1 ≤ U) (hc : 0 ≤ γ) (k : ℕ) (hg : γ+k*δ ≤ σ)
    (hb : l₁.length ≤ k) (hv : l₂.length ≤ k)
    (hw : ∀ x, C.pay l x=C.pay l₁ x*C.pay l₂ x) (hm : 0 ≤ M) (hN : 0 ≤ N)
    (hp : Bill C D a b l₁ σ M A) (hq : Bill C D b c l₂ σ N B) : Bill C D a c l γ (U^k*M*N) (A*B) := by
  have he : ∀ i : ℕ, i ≤ k → γ+i*δ ≤ σ := fun i hi => le_trans (add_le_add_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hn) _) hg
  have hl : γ ≤ σ := le_trans (le_add_of_nonneg_right (by positivity)) hg
  constructor
  · apply (hp.row.mul h (zero_le_one.trans hu) hc (he _ hv) hw (hq.row.mono hl le_rfl) hN).mono le_rfl
    rw [mul_right_comm _ M]; gcongr
  rw [Matrix.transpose_mul]
  apply (hq.col.mul h (zero_le_one.trans hu) hc (he _ hb) (fun x => by rw [mul_comm]; exact hw x) (hp.col.mono hl le_rfl) hm).mono le_rfl
  gcongr

lemma of_entry (hV : D.Volume b (σ-γ) N) (hV' : D.Volume a (σ-γ) N)
    (hM : 0 ≤ M)
    (h : ∀ i j, C.pay l (a i)*(D.weight σ (a i) (b j)*|A i j|) ≤ M)
    (h' : ∀ i j, C.pay l (b j)*(D.weight σ (b j) (a i)*|A i j|) ≤ M) :
    Bill C D a b l γ (N*M) A := ⟨Rates.of_entry hV hM h, Rates.of_entry hV' hM fun i j => h' j i⟩
end Bill
end both

/-- Test input growth in  convention, using *the projected initial
site*. Arbitrary external direction labels. Use smaller exponential debt
as needed at EACH evaluation, never depend on period. -/
def radial (τ : Type*) (D : Cost X) (o : X) (P : ℕ) : Mark τ X :=
  ⟨fun _ x => ((1+D.d x o)^P)⁻¹, fun _ x => inv_pos.mpr (pow_pos (by have := D.nonneg x o; linarith) _)⟩

-- elementary polynomial debt at explicit width, even P=0
def polynomial (δ : ℝ) (P : ℕ) := (1+(δ/(P+1:ℕ))⁻¹)^P
lemma poly_le {δ : ℝ} (P : ℕ) (hδ : 0 < δ) : 1 ≤ polynomial δ P :=
  one_le_pow₀ (le_add_of_nonneg_right (by positivity))
lemma poly_weight {d δ : ℝ} (P : ℕ) (hδ : 0 < δ) (hd : 0 ≤ d) :
    (1+d)^P ≤ polynomial δ P * Real.exp (δ*d) := by
  let x : ℝ := δ/(P+1:ℕ)
  have hx : 0 < x := by unfold x; positivity
  have hp : Real.exp (x*d) ≥ 1 := Real.one_le_exp (by positivity)
  have he : 1+d ≤ (1+x⁻¹)*Real.exp (x*d) := by
    have he : d ≤ x⁻¹ * Real.exp (x*d) := by
      rw [inv_mul_eq_div, le_div_iff₀ hx]
      linarith only [Real.add_one_le_exp (x*d)]
    rw [add_mul,one_mul]; exact add_le_add hp he
  apply (pow_le_pow_left₀ (by linarith : 0 ≤ 1+d) he P).trans
  rw [mul_pow, ← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_monotone
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hd
  unfold x; push_cast; rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  linarith

lemma radial_move (τ : Type*) (o : X) (P : ℕ) (hδ : 0 < δ) : Move (radial τ D o P) D δ (polynomial δ P) := by
  constructor; intro t x y
  let A := 1+D.d x o
  let B := 1+D.d y o
  have ha : 0 < A := by unfold A; have := D.nonneg x o; linarith
  have hb : 0 < B := by unfold B; have := D.nonneg y o; linarith
  have hh : B^P ≤ (polynomial δ P*D.weight δ x y)*A^P := by
    calc
      _ ≤ ((1+D.d x y)*A)^P := pow_le_pow_left₀ hb.le (by unfold B A; nlinarith only [D.triangle y x o,D.comm y x, mul_nonneg (D.nonneg x y) (D.nonneg x o)]) P
      _ = (1+D.d x y)^P*A^P := mul_pow ..
      _ ≤ (polynomial δ P*D.weight δ x y)*A^P := mul_le_mul_of_nonneg_right (poly_weight P hδ (D.nonneg ..)) (by positivity)
  change (A^P)⁻¹ ≤ _ * (B^P)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hb _), inv_mul_eq_div, div_le_iff₀ (pow_pos ha _)]; exact hh

/-- Track *locations* of each Taylor index for tensor use. -/
def positions (D : Cost X) (w : τ → X) (δ : ℝ) : Mark τ X := ⟨fun t x => D.weight δ x (w t), fun _ _ => D.weight_pos ..⟩
lemma position_move (D : Cost X) (w : τ → X) (hn : 0 ≤ δ) : Move (positions D w δ) D δ 1 := by
  constructor; intro t x y; rw [one_mul]; exact D.weight_triangle hn ..
end Mark
end YM.FreeResolvent
