import YM.Next.RANK.GaussTrack
import YM.Next.RANK.Rise


/-!
# Pointwise costs/comparison on *finite* W polynomials

Pull over-charge uniform K cap into coordinates BEFORE moment expansion. Only
parameter losses polynomial in degree ceiling powers (may use p^{o(1)} once).
Dimension-independent costs suffice. Mean unscaled; same-field values pre vs post
normal-ordered kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Common
open Function MvPolynomial Finset Normal Rise
open scoped BigOperators Classical

variable {A V : Type*} {Q Q' : Symmetric V} {m m' : V → ℂ} {B E : ℝ}

-- means, symmetric samples; may also use over coarse geometry even over dead coordinates.

structure Sorts (Q : Symmetric V) (m : V → ℂ) (B : ℝ) : Prop where
  paid : 1≤B
  mean i : ‖m i‖ ≤ B
  entries i j : ‖Q.cov i j‖≤B

structure Nearby (Q Q' : Symmetric V) (m m' : V → ℂ) (B E : ℝ) : Prop where
  small : Sorts Q m B
  small' : Sorts Q' m' B
  pos : 0 ≤ E
  mean i : ‖m i-m' i‖ ≤ E
  cov i j : ‖Q.cov i j-Q'.cov i j‖ ≤ E

-- crude but degree-continuous bound. use $((2B)(d+1))^d$ for both. -

def priced (B : ℝ) (d : ℕ) := ((2*B)*(d+1:ℝ))^d

private lemma finds [DecidableEq A] (Z : A → V) (d : ℕ) (p : Finset A) (h : Sorts Q m B) (hp : p.card ≤ d) :
    ‖blend Q m (glyphs Z p)‖≤ priced B d := by
  induction d generalizing p with
  | zero => have he := card_eq_zero.mp (Nat.eq_zero_of_le_zero hp); subst p; simp only [glyphs,prod_empty,fresh,priced,pow_zero,norm_one,le_refl]
  | succ d IH =>
    let c := priced B d
    have hb := zero_lt_one.trans_le h.paid
    have ht : 0 ≤ c := by dsimp only [c,priced]; positivity
    obtain rfl|⟨i,hi⟩ := p.eq_empty_or_nonempty
    · simp only [glyphs,prod_empty,fresh,norm_one]; apply one_le_pow₀; have hz := h.paid; push_cast; nlinarith
    let s:= p.erase i
    have hv : s.card ≤ d := by dsimp only [s]; rw [card_erase_of_mem hi]; omega
    have h2 : ‖∑ j∈s,Q.cov (Z i) (Z j) * blend Q m (glyphs Z (s.erase j))‖ ≤ (d:ℝ)*(B*c) := by
      apply (norm_sum_le ..).trans
      calc
        _ ≤ ∑ _∈s, B*c := by
          apply sum_le_sum; intro j _; rw [norm_mul]; exact mul_le_mul (h.entries ..) (IH _ ((card_le_card (erase_subset ..)).trans hv)) (norm_nonneg _) hb.le
        _ ≤ _ := by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hv) (mul_nonneg hb.le ht)
    rw [show p=insert i s from (insert_erase hi).symm, spring ..]; rotate_left; exact notMem_erase _ _
    apply (norm_add_le ..).trans; rw [norm_mul]
    apply (add_le_add (mul_le_mul (h.mean _) (IH _ hv) (norm_nonneg _) hb.le) h2).trans
    change B*c+d*(B*c) ≤ priced B _
    unfold priced; push_cast; rw [pow_succ]
    have ht' : c ≤ (2*B*(↑d+1+1))^d := by dsimp only [c,priced]; gcongr; exact le_add_of_nonneg_right zero_le_one
    refine le_trans ?_ (mul_le_mul_of_nonneg_right ht' ?_)
    · nlinarith only [mul_nonneg hb.le ht,zero_le_one' ℝ,mul_nonneg (Nat.cast_nonneg d) (mul_nonneg hb.le ht)]
    positivity

private lemma compare_pair {x y v w : ℂ} {b a E C : ℝ} (hx : ‖x-y‖ ≤ a) (hb : ‖x‖ ≤ b) (hw : ‖w‖ ≤ C) (he : ‖v-w‖ ≤ E) :
    ‖x*v-y*w‖ ≤ b*E +a*C := by
  rw [show x*v-y*w=x*(v-w)+(x-y)*w by ring]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; exact add_le_add
    (mul_le_mul hb he (norm_nonneg _) ((norm_nonneg _).trans hb)) (mul_le_mul hx hw (norm_nonneg _) ((norm_nonneg _).trans hx))

private lemma crosses [DecidableEq A] (Z : A → V) (d : ℕ) (p : Finset A) (hp : p.card ≤ d) (h : Nearby Q Q' m m' B E) :
    ‖blend Q m (glyphs Z p)-blend Q' m' (glyphs Z p)‖ ≤ E*priced B d := by
  induction d generalizing p with
  | zero => have he := card_eq_zero.mp (Nat.eq_zero_of_le_zero hp); subst p; simpa only [glyphs,prod_empty,fresh,sub_self, priced,pow_zero,norm_zero,mul_one] using h.pos
  | succ d IH =>
    let c := priced B d
    have hb := zero_lt_one.trans_le h.small'.paid; have hh := h.pos
    have ht : 0 ≤ c := by dsimp only [c,priced]; positivity
    obtain rfl|⟨i,hi⟩ := p.eq_empty_or_nonempty
    · simp only [glyphs,prod_empty,fresh,sub_self,norm_zero,priced]; positivity
    let s:= p.erase i
    have hv : s.card ≤ d := by dsimp only [s]; rw [card_erase_of_mem hi]; omega
    have h2 : ‖(∑ j∈s,Q.cov (Z i) (Z j)*blend Q m (glyphs Z (s.erase j))) -
        (∑ j∈s,Q'.cov (Z i) (Z j)*blend Q' m' (glyphs Z (s.erase j)))‖ ≤ (d:ℝ)*(B*(E*c)+E*c) := by
      rw [← Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans
      calc
        _ ≤ ∑ j∈s, (B*(E*c)+E*c) := by
          apply sum_le_sum; intro j _; have hn := (card_le_card (erase_subset j s)).trans hv
          exact compare_pair (h.cov ..) (h.small.entries ..) (finds Z d _ h.small' hn) (IH _ hn)
        _ ≤ _ := by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hv) (by positivity)
    have he : i ∉ s := notMem_erase _ _
    rw [show p=insert i s from (insert_erase hi).symm, spring _ _ _ _ he,spring _ _ _ _ he,add_sub_add_comm]
    apply (norm_add_le ..).trans; apply (add_le_add (compare_pair (h.mean _) (h.small.mean _) (finds Z d _ h.small' hv) (IH _ hv)) h2).trans
    change B*(E*c)+E*c + d*(B*(E*c)+E*c) ≤ _
    unfold priced; push_cast; rw [pow_succ]
    have ht' : c ≤ (2*B*(↑d+1+1))^d := by dsimp only [c,priced]; gcongr; exact le_add_of_nonneg_right zero_le_one
    have hn : E*c ≤ B*(E*c) := le_mul_of_one_le_left (by positivity) h.small.paid
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht' (by positivity)) hh)
    nlinarith only [hn,mul_le_mul_of_nonneg_left hn (show (0:ℝ) ≤ d by positivity),mul_nonneg hb.le (mul_nonneg hh ht)]

lemma letter (i : V →₀ ℕ) :
    let n := i.sum (fun _ k => k)
    ∃ v : Fin n → V,(monomial i 1 : poly V) = glyphs v univ := by
  classical
  intro n; let U := (k : i.support) × Fin (i k.val)
  have hh : Fintype.card U=n := by
    dsimp only [n,Finsupp.sum]; simp only [U,Fintype.card_sigma,Fintype.card_fin]; exact Finset.sum_attach ..
  let w := Fintype.equivFinOfCardEq hh
  let H (z : U) := X (R:=ℂ) z.1.val
  let v := fun (k : Fin n) => (w.symm k).1.val
  refine ⟨v,?_⟩
  have he : (∏ z:U,H z)=glyphs v univ := Fintype.prod_equiv w H _ (fun i => by simp only [v,Equiv.symm_apply_apply,H])
  rw [← he,Fintype.prod_sigma H,monomial_eq,map_one,one_mul,Finsupp.prod]
  simp only [H,prod_const,card_univ,Fintype.card_fin]; exact (Finset.prod_attach i.support (fun k => X k ^ i k)).symm

lemma to_basis (L : poly V→ₗ[ℂ] ℂ) (p : poly V) {A : ℝ} (h : ∀ i∈p.support, ‖L (monomial i 1)‖≤A) : ‖L p‖ ≤ coin p * A := by
  nth_rw 1 [MvPolynomial.as_sum p]; rw [map_sum]; apply (norm_sum_le ..).trans; rw [metal,Finset.sum_mul]
  apply sum_le_sum; intro i hi; have ht : monomial i (coeff i p) = coeff i p • monomial i (1:ℂ) := by rw [← map_smul, smul_eq_mul,mul_one]
  rw [ht,map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (h i hi) (norm_nonneg _)

lemma width (p : poly V) (d : ℕ) (h : Sorts Q m B) (hp : p.totalDegree ≤ d) :
    ‖blend Q m p‖ ≤ coin p * priced B d := to_basis _ _ fun i hi => by
  obtain ⟨v,ht⟩ := letter i; rw [ht]; apply finds v d _ h; simpa using (le_totalDegree hi).trans hp
lemma differs (p : poly V) (d : ℕ) (h : Nearby Q Q' m m' B E) (hp : p.totalDegree ≤ d) :
    ‖blend Q m p-blend Q' m' p‖≤coin p * (E*priced B d) := to_basis ((blend Q m)-(blend Q' m')) p fun i hi => by
  obtain ⟨v,ht⟩ := letter i; rw [ht]; exact crosses v d _ (by simpa using (le_totalDegree hi).trans hp) h
end YM.Next.Rank.Common
