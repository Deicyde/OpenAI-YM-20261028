import YM.RG08.Ward.Evergreen

/-!
# One block kinetic ratio: solve formally in independent Wilson branch
Unscaled `a = g_f², b = g_c²`, precision multiplier `Ω(a)`, solve
`a=b R(b), R=Ω(a)` in ordinary Taylor series. No analytic dependence
of continuum limit or physical coupling scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Conductor
open PowerSeries Function Finset Filter
open scoped BigOperators Topology Real Classical

variable (W : ℕ→ℝ) {v : ℕ→ℝ}

def powT (V : ℕ→ℝ) (i j : ℕ) := coeff j (PowerSeries.mk V ^ i)
lemma pow_zeroT (V : ℕ→ℝ) (j) : powT V 0 j=if j=0 then 1 else 0 := by simp [powT,PowerSeries.coeff_one]
lemma pow_suit (V : ℕ→ℝ) (i j) : powT V (i+1) j=∑ p∈wheel j,powT V i p.1 * V p.2 := by simp only [powT,pow_succ, coeff_mul, coeff_mk]
lemma powT_local {v w : ℕ→ℝ} {n : ℕ}(h : ∀ i<n,v i=w i) (p j) (hj : j<n) : powT v p j=powT w p j := by
  induction p generalizing j with
  | zero=> rw [pow_zeroT,pow_zeroT]
  | succ p ih=> rw [pow_suit,pow_suit]; apply sum_congr rfl; intro i hi; rw [ih,h i.2] <;> have hp:=mem_antidiagonal.mp hi <;> omega

def reform (n : ℕ) : ℝ := match n with
  | 0=> W 0
  | n+1=> ∑ j ∈ range (n+1), W (j+1) * powT (fun k=> if k<n+1 then reform k else 0) (j+1) (n-j)
termination_by n
decreasing_by all_goals omega
-- include W recursive explicit needed
lemma reform_zero : reform W 0=W 0 := by rw [reform]
lemma reform_succ (n) : reform W (n+1)= ∑ j∈range (n+1),W (j+1)*powT (reform W) (j+1) (n-j) := by
  rw [reform]; apply sum_congr rfl; intro i hi
  apply congr_arg (W (i+1)*·); exact powT_local (n:=n+1) (fun i hi=> by rw [if_pos hi]) _ _ (by omega)
lemma reform_cast (n) : reform W n= ∑ j∈range (n+1), W j * powT (reform W) j (n-j) := by
  cases n with
  | zero=> rw [reform_zero]; simp [pow_zeroT]
  | succ n=> rw [reform_succ,sum_range_succ' (n:=n+1)]; simp [pow_zeroT]

abbrev Span (V : ℕ→ℝ) : PowerSeries ℝ := X* PowerSeries.mk V
lemma spanning {V : ℕ→ℝ} : HasSubst (Span V) := .of_constantCoeff_zero (by change constantCoeff (X * PowerSeries.mk V)=0; simp)
lemma merge_f {V : ℕ→ℝ}(n) : coeff n (PowerSeries.subst (Span V) (PowerSeries.mk W))= ∑ j∈range (n+1), W j * powT V j (n-j) := by
  rw [coeff_subst' spanning, finsum_eq_sum_of_support_subset _]
  · apply Finset.sum_congr rfl; intro j hj; rw [coeff_mk, Span,mul_pow, coeff_X_pow_mul',if_pos (Nat.le_of_lt_succ (mem_range.mp hj))]; rfl
  intro j hj; by_contra hp; simp only [mem_coe, mem_range, not_lt] at hp
  exact hj (by dsimp only; unfold Span; rw [mul_pow, coeff_X_pow_mul',if_neg (by omega),smul_zero])

lemma reforms : PowerSeries.mk (reform W)=PowerSeries.subst (Span (reform W)) (PowerSeries.mk W) := by apply PowerSeries.ext; intro i; rw [coeff_mk,reform_cast,merge_f]
lemma unique_reform (h : PowerSeries.mk v=PowerSeries.subst (Span v) (PowerSeries.mk W)) : v=reform W := by
  have he i : v i= ∑ j∈range (i+1), W j * powT v j (i-j) := by conv_lhs=>rw [←  show coeff i (PowerSeries.mk v)=v i from PowerSeries.coeff_mk .., h]; exact merge_f ..
  funext i; induction i using Nat.caseStrongRecOn with
  | zero=> simpa [pow_zeroT,reform_zero W] using he 0
  | ind n ih=> rw [he (n+1),reform_succ,sum_range_succ' _ (n+1)]; simp only [pow_zeroT,tsub_zero,Nat.add_eq_zero_iff, Nat.one_ne_zero,and_false, ↓reduceIte,mul_zero,add_zero]; apply sum_congr rfl; intro i hi; rw [show n+1-(i+1)=n-i by omega]; exact congr_arg _ (powT_local (n:=n+1) (fun i hi=>ih i (by omega)) _ _ (by omega))

-- Teal: splays arbitrary punch AFTER undoing extracted power a once.
private lemma reflux_f {V p : ℕ→ℝ} (n) : coeff n ((PowerSeries.mk V)⁻¹ * PowerSeries.subst (Span V) (PowerSeries.mk p))=
    ∑ j∈range (n+1), p j * coeff (n-j) ((PowerSeries.mk V)⁻¹ * PowerSeries.mk V ^ j) := by
  let a:=PowerSeries.mk p; let w:=PowerSeries.mk V
  let b:= ∑ j∈range (n+1), C (p j)*(X*w)^j
  have H i (hi:i≤n) : coeff i b=coeff i (PowerSeries.subst (Span V) a) := by
    unfold b a; rw [map_sum,merge_f]; simp_rw [coeff_C_mul,mul_pow,coeff_X_pow_mul']; symm
    let S j:= p j * if j ≤ i then coeff (i-j) (w^j) else 0
    calc
      _ = ∑ j∈range (i+1), S j := sum_congr rfl fun j hj=> by unfold S; rw [if_pos (by have ht:=mem_range.mp hj; omega)]; rfl
      _ = _ := Finset.sum_subset (range_mono (by omega: i+1≤n+1)) (fun j _ hj=> by simp only [mem_range] at hj; unfold S; rw [if_neg (by omega),mul_zero])
  have ht : coeff n (w⁻¹*b)=coeff n (w⁻¹*PowerSeries.subst (Span V) a) := by rw [coeff_mul,coeff_mul]; apply sum_congr rfl; intro i hi; rw [H i.2 (by have ht:=mem_antidiagonal.mp hi; omega)]
  rw [← ht]; unfold b; rw [Finset.mul_sum,map_sum]; apply sum_congr rfl; intro j hj
  -- distribute and shift prefix
  rw [mul_pow,show w⁻¹*(C (p j)*(X^j*w^j))=C (p j)*(X^j*(w⁻¹*w^j)) by ring,coeff_C_mul,coeff_X_pow_mul',if_pos (by have ht:=mem_range.mp hj; omega)]

def recitalR (W : ℕ→ℝ) (q k : ℕ) : ℝ := match k with
  | 0=> coeff q (PowerSeries.mk (reform W))⁻¹
  | k+1=>powT (reform W) k (q-(k+1))

lemma recital_priced (hW : W 0=1) (k : ℕ) : recitalR W k k=1 := by
  cases k with
  | zero=> unfold recitalR; simp only [coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,constantCoeff_mk,reform_zero,hW,inv_one]
  | succ k=> rw [recitalR]; simp [powT,coeff_zero_eq_constantCoeff_apply,constantCoeff_mk,reform_zero,hW] -- need simp h
-- equality to Laurent substitution; applies e.g. evaluated separately at each rank/cell
lemma rewrite_back (hW : W 0=1) (p : ℕ→ℝ) (q) : coeff q ((PowerSeries.mk (reform W))⁻¹ * PowerSeries.subst (Span (reform W)) (PowerSeries.mk p))=∑ k∈range (q+1), recitalR W q k*p k := by
  rw [reflux_f]; apply sum_congr rfl; intro j hj
  cases j with
  | zero=> simp [recitalR,mul_comm]
  | succ j=> unfold recitalR powT; rw [pow_succ', ← mul_assoc, PowerSeries.inv_mul_cancel,one_mul,mul_comm]; rw [constantCoeff_mk,reform_zero,hW]; simp
lemma restored (hW : W 0=1) (q) : ∑ k∈range (q+1), recitalR W q k*W k= if q=0 then 1 else 0 := by rw [← rewrite_back W hW,← reforms, PowerSeries.inv_mul_cancel,coeff_one]; rw [constantCoeff_mk,reform_zero,hW]; simp
end YM.RG08.Conductor
