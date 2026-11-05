import YM.Next.RANK.GaussTags

/-! Weighted L1 of endpoint polynomials. These need no labels off finite
supports and use any generation function. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Rise
open Function Finset MvPolynomial Normal
open scoped Topology BigOperators Classical

variable {V Z A : Type*}

def cents (p : poly V) (w : V → ℕ) (r : ℝ) : ℝ := ∑ i∈p.support,r^((Finsupp.weight w) i)*‖coeff i p‖
lemma sign (w : V → ℕ) {r : ℝ} (p : poly V) (h : 0 ≤ r) : 0 ≤ cents p w r := sum_nonneg fun _ _ => mul_nonneg (pow_nonneg h _) (norm_nonneg _)
lemma tavern (b : ℂ) (z : V →₀ ℕ) (w : V → ℕ) (r : ℝ) : cents (monomial z b) w r=r^(Finsupp.weight w z)*‖b‖ := by
  unfold cents; rw [← MvPolynomial.sum_def (p:=monomial z b) (b:=fun i (x:ℂ) => r^(Finsupp.weight w i)*‖x‖)]; exact MvPolynomial.sum_monomial_eq (by simp)
@[simp] lemma pay_nothing (w : V → ℕ) (r : ℝ) : cents (0 : poly V) w r=0 := by simp [cents]
@[simp] lemma pay_C (w : V → ℕ) (r : ℝ) (i : ℂ) : cents (C i) w r= ‖i‖ := by
  rw [show C i=(monomial 0 i : poly V) from rfl,tavern,map_zero]; simp
@[simp] lemma pay_one (w : V → ℕ) (r : ℝ) : cents (1:poly V) w r=1 := by rw [← show C 1=(1:poly V) from map_one _,pay_C,norm_one]
@[simp] lemma pay_X (w : V → ℕ) (r : ℝ) (i : V) : cents (X i) w r= r^(w i) := by rw [X,tavern,Finsupp.weight_single]; simp

lemma taller (w : V → ℕ) {r : ℝ} (h : 0 ≤ r) (p q : poly V) : cents (p+q) w r≤cents p w r+cents q w r := by
  let m (g : poly V) i := r^(Finsupp.weight w i)*‖coeff i g‖
  let A := p.support ∪ q.support
  have he (g : poly V) (hx : g.support ⊆ A) : cents g w r=∑ i∈A,m g i := sum_subset hx fun i _ hp => by simp only [MvPolynomial.notMem_support_iff.mp hp,norm_zero,mul_zero]
  rw [he (p+q) MvPolynomial.support_add,he p subset_union_left,he q subset_union_right, ← sum_add_distrib]; apply sum_le_sum; intro i _
  dsimp only [m]; rw [← mul_add,coeff_add]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (pow_nonneg h _)
lemma collect (w : V → ℕ) {r : ℝ} (h : 0 ≤ r) (s : Finset Z) (f : Z → poly V) : cents (∑ i∈s,f i) w r ≤ ∑ i∈s,cents (f i) w r := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [sum_insert hi,sum_insert hi]; exact (taller w h (f i) _).trans (add_le_add_right ih _)
lemma funds (w : V → ℕ) {r : ℝ} (h : 0 ≤ r) (p q : poly V) : cents (p*q) w r≤cents p w r*cents q w r := by
  rw [MvPolynomial.mul_def]; simp_rw [MvPolynomial.sum_def]
  apply (collect w h _ _).trans; change _ ≤ (∑ i∈p.support,r^(Finsupp.weight w i)*‖coeff i p‖)*(∑ i∈q.support,r^(Finsupp.weight w i)*‖coeff i q‖)
  rw [Finset.sum_mul_sum]; apply sum_le_sum; intro i _
  apply (collect w h _ _).trans; refine sum_le_sum fun j _ => ?_; rw [tavern,map_add,norm_mul,pow_add]; exact le_of_eq (by ring)
lemma purchased (w : V → ℕ) {r : ℝ} (h : 0 ≤ r) (s : Finset Z) (f : Z → poly V) : cents (∏ i∈s,f i) w r ≤ ∏ i∈s,cents (f i) w r := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [prod_insert hi,prod_insert hi]; exact (funds w h _ _).trans (mul_le_mul_of_nonneg_left ih (sign w _ h))
lemma iterated (w : V → ℕ) {r : ℝ} (h : 0 ≤ r) (p : poly V) (n : ℕ) : cents (p^n) w r ≤ (cents p w r)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,pow_succ]; exact (funds w h _ _).trans (mul_le_mul_of_nonneg_right ih (sign w _ h))

abbrev coin (p : poly V) := cents p 0 1
lemma metal (p : poly V) : coin p=∑ i∈p.support,‖coeff i p‖ := by simp [coin,cents]

-- use only finite ℓ¹ weights at old array. account once per vertex.
lemma rise (e : V → Z →₀ ℂ) (w : Z → ℕ) {r c : ℝ} (hr : 0 ≤ r) (hc : 1 ≤ c) (h : ∀ i,cents (glyph (e i)) w r ≤ c) (p : poly V) {d : ℕ} (hp : p.totalDegree ≤ d) :
    cents (exchange e p) w r ≤ coin p * c^d := by
  classical
  suffices ∀ i∈p.support,cents (exchange e (monomial i (coeff i p))) w r ≤ ‖coeff i p‖ * c^d by
    nth_rw 1 [p.as_sum]; rw [map_sum]
    refine (collect w hr _ _).trans ?_; rw [metal, Finset.sum_mul]; exact sum_le_sum this
  intro i hi
  let a := coeff i p
  let Q (z) := e z
  rw [monomial_eq,map_mul,exchange_c]
  apply (funds w hr _ _).trans
  rw [pay_C]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simp_rw [Finsupp.prod,map_prod,map_pow,exchange_x]
  refine (purchased w hr _ _).trans ((prod_le_prod (fun i _ => sign w _ hr) (fun j _ =>
    (iterated w hr _ _).trans (pow_le_pow_left₀ (sign w (glyph _) hr) (h j) (i j)))).trans ?_)
  rw [prod_pow_eq_pow_sum]; exact pow_le_pow_right₀ hc ((le_totalDegree hi).trans hp)

lemma port (i : A) (p : poly V) : coin (post i p) ≤ coin p := by
  unfold post; rw [Normal.labelled]
  apply (rise (fun y : V => Finsupp.single (i,y) 1) 0 zero_le_one le_rfl ?_ p (le_refl _)).trans
  · simp only [one_pow,mul_one,le_refl]
  intro j; simp

lemma ascent (e : V → Z →₀ ℂ) (p : poly V) : totalDegree (exchange e p) ≤ totalDegree p := by
  nth_rw 1 [p.as_sum]; rw [map_sum]; refine (totalDegree_finsetSum _ _).trans (Finset.sup_le ?_); intro i hi
  rw [monomial_eq, map_mul,exchange_c]; apply (totalDegree_mul ..).trans
  simp_rw [totalDegree_C,zero_add,Finsupp.prod,map_prod,map_pow,exchange_x]
  have hc (z) : totalDegree (glyph (e z)) ≤ 1 := by
    unfold glyph; rw [Finsupp.linearCombination_apply,Finsupp.sum]; exact (totalDegree_finsetSum _ _).trans (Finset.sup_le (fun j _ => (totalDegree_smul_le ..).trans_eq (totalDegree_X _)))
  refine (totalDegree_finsetProd ..).trans (le_trans (sum_le_sum fun j _ => ?_) (le_totalDegree hi))
  exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left _ (hc _)).trans (Nat.mul_one _).le)

-- take high powers out when P fixed.

def trim (p : poly V) (w : V → ℕ) (d : ℕ) := ∑ i∈p.support.filter (fun i => Finsupp.weight w i ≤ d), monomial i (coeff i p)
lemma above (p : poly V) (w : V → ℕ) (d : ℕ) : p-trim p w d=
    ∑ i∈p.support.filter (fun i => ¬ Finsupp.weight w i ≤ d),monomial i (coeff i p) := by
  rw [sub_eq_iff_eq_add',trim,sum_filter_add_sum_filter_not]; exact as_sum p
lemma ridge (p : poly V) (w : V → ℕ) (d : ℕ) {r : ℝ} (h : 1≤r) :
    coin (p-trim p w d)*r^(d+1) ≤ cents p w r := by
  rw [above]; apply (mul_le_mul_of_nonneg_right (collect 0 zero_le_one _ _) (pow_nonneg (zero_le_one.trans h) _)).trans
  rw [sum_mul]; change _ ≤ (∑ i∈p.support,r^(Finsupp.weight w i)*‖coeff i p‖)
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg (filter_subset (fun i => ¬ Finsupp.weight w i ≤ d) (p.support)) (fun i _ _ =>
    show 0 ≤ r^(Finsupp.weight w i) * ‖coeff i p‖ from mul_nonneg (pow_nonneg (zero_le_one.trans h) _) (norm_nonneg _)))
  apply sum_le_sum; intro i hi
  have he := mem_filter.mp hi|>.2
  change coin (monomial i _) * _ ≤ _
  rw [coin,tavern,one_pow,one_mul,mul_comm]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h (show _+1≤_ from Nat.lt_of_not_ge he)) (norm_nonneg _)

lemma trim_coeff [DecidableEq V] (p : poly V) (w : V → ℕ) (d : ℕ) (i : V →₀ ℕ) :
    coeff i (trim p w d)=if Finsupp.weight w i ≤ d then coeff i p else 0 := by
  rw [trim,coeff_sum]; by_cases h : Finsupp.weight w i ≤ d
  · rw [if_pos h,sum_eq_single i, coeff_monomial]; simp only [↓reduceIte]
    · intro b _ hb; rw [coeff_monomial,if_neg hb]
    intro hp; exact (coeff_monomial ..).trans ((if_pos rfl).trans (MvPolynomial.notMem_support_iff.mp (fun hh => hp (mem_filter.mpr ⟨hh,h⟩))))
  rw [if_neg h]; exact sum_eq_zero fun j hj => (coeff_monomial ..).trans (if_neg (fun (he : j=i) => h (he ▸ (mem_filter.mp hj).2)))

lemma below_degree (p : poly V) (w : V → ℕ) (d : ℕ) : totalDegree (trim p w d) ≤ p.totalDegree := by
  unfold trim; exact (totalDegree_finsetSum ..).trans (Finset.sup_le fun i hi => (totalDegree_monomial_le ..).trans (le_totalDegree (mem_filter.mp hi).1))
end YM.Next.Rank.Rise
