import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Next.MULTISOURCE.Decal


/-!
# Prices from pointwise polynomial tests. Uniform control on jets by finite DFT

Need interior only for actual convergence; for pricing may also use degenerate
polydiscs on coordinates OFF the coefficient. Use normalized DFT so no
number-of-phases price. No taking maxima of radius-dependent scalar slots
and assuming their sum is small.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Desk
open MvPolynomial Function Finset Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Cir (I : Type*) (n : ℕ) := I → Fin n

def twirl (n : ℕ) := Complex.exp (2*(Real.pi:ℂ)*Complex.I/n)
lemma primitive {n : ℕ} (h : 0<n) : IsPrimitiveRoot (twirl n) n := Complex.isPrimitiveRoot_exp n h.ne'
lemma tone {n : ℕ} (h : 0<n) : ‖twirl n‖ = 1 := (primitive h).norm'_eq_one h.ne'

def looped (r : I → ℝ) (n : ℕ) (p : Cir I n) (i : I) := (r i:ℂ)* twirl n ^ (p i).val

def price (r : I → ℝ) (x : Grade I) := ∏ i, r i^x i

omit [Fintype I] [DecidableEq I] in
lemma circle_val (r : I → ℝ) (n : ℕ) (p : Cir I n) (hr : ∀ i, 0 ≤ r i) (h : 0 < n) (i : I) :
    ‖looped r n p i‖ = r i := by
  simp only [looped, norm_mul, norm_pow, tone h, one_pow,mul_one,Complex.norm_real,
    Real.norm_of_nonneg (hr i)]

lemma price_pos (r : I → ℝ) (x : Grade I) (hp : ∀ i∈ x.support,0 < r i) : 0 < price r x := by
  apply prod_pos; intro i _
  by_cases h : i∈x.support
  · exact pow_pos (hp i h) _
  rw [Finsupp.notMem_support_iff.mp h,pow_zero]; exact zero_lt_one

lemma reaches (r : I→ℝ) (s : Finset I) : price r (power s)=∏ i∈s,r i := by
  unfold price
  have he (i : I) : r i ^ power s i = if i∈s then r i else 1 := by
    rw [power_apply]; split <;> simp_all
  simp_rw [he, ← Finset.prod_filter]; simp

omit [DecidableEq I] in
def hop (n : ℕ) (p : Cir I n) (x : Grade I) := ∏ i, (twirl n ^ (p i).val) ^ (x i)

omit [DecidableEq I] in
lemma hop_norm (n : ℕ) (p : Cir I n) (x : Grade I) (h : 0<n) : ‖hop n p x‖=1 := by
  unfold hop; rw [norm_prod]; simp [tone h]

private lemma arches {a b N : ℕ} (hx : a < N) (hy : b < N) :
    ∑ i : Fin N, (((twirl N ^ i.val)^a)⁻¹ * (twirl N ^ i.val)^b)=if a=b then (N:ℂ) else 0 := by
  let c := twirl N
  have hp := primitive (Nat.zero_lt_of_lt hx)
  have hh : c ≠ 0 := Complex.exp_ne_zero _
  by_cases h : a=b
  · subst b; simp [Complex.exp_ne_zero,twirl]
  rw [if_neg h]
  have hv (i) : ((twirl N ^ i)^a)⁻¹ * (twirl N ^ i)^b=(c^b / c^a)^ (i : ℕ) := by
    unfold c
    rw [div_pow, div_eq_mul_inv, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,Nat.mul_comm i a,Nat.mul_comm i b,mul_comm]
  simp_rw [hv]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq]
  · have hu : ∀ j : ℕ,(c^j)^N=1 := fun j => by
      rw [← pow_mul,Nat.mul_comm,pow_mul,hp.pow_eq_one,one_pow]
    rw [div_pow,hu,hu,div_one,sub_self,zero_div]
  intro ht; exact h ((hp.pow_inj hy hx ((div_eq_one_iff_eq (pow_ne_zero _ hh)).mp ht)).symm)

lemma isolates (x y : Grade I) (N : ℕ) (hp : ∀ i,x i < N) (hy : ∀ i,y i < N) :
    ∑ i : Cir I N, (hop N i x)⁻¹ * hop N i y=if x=y then (Fintype.card (Cir I N) : ℂ) else 0 := by
  simp_rw [hop,← Finset.prod_inv_distrib,← prod_mul_distrib,← Fintype.prod_sum (fun i (j : Fin N) =>
    (((twirl N^j.val)^x i)⁻¹ * (twirl N^j.val)^y i)), arches (hp _) (hy _)]
  split
  · rename_i e; subst y
    simp only [if_true,prod_const,card_univ,Cir,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  rename_i e
  obtain ⟨i,hi⟩ : ∃ i,x i ≠ y i := by by_contra! h; exact e (Finsupp.ext h)
  exact prod_eq_zero (mem_univ i) (if_neg hi)

def load (r : I→ℝ) (N : ℕ) (p : Cir I N) (x : Grade I) :=
    (price r x:ℂ)⁻¹ * (Fintype.card (Cir I N):ℂ)⁻¹ * (hop N p x)⁻¹

lemma total (r : I→ℝ) (x : Grade I) {N : ℕ} (hp : 0 < price r x) (h : 0 < N) :
    (∑ i : Cir I N, ‖load r N i x‖)=(price r x)⁻¹ := by
  haveI : Nonempty (Fin N) := ⟨⟨0,h⟩⟩
  have hn : 0 < (Fintype.card (Cir I N) : ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [load, norm_mul, norm_inv, Complex.norm_real, hop_norm _ _ _ h, Complex.norm_natCast,
    Real.norm_of_nonneg hp.le, inv_one,mul_one,sum_const,card_univ,nsmul_eq_mul]
  field_simp

lemma display (r : I → ℝ) (x : Grade I) {N : ℕ} (p : Wave I) (h : 0 < N) (hp : 0 < price r x)
    (he : ∀ i,x i < N) (hh : ∀ y ∈ p.support, ∀ i,y i < N) :
    coeff x p = ∑ i : Cir I N, load r N i x * eval (looped r N i) p := by
  have hx (γ : Grade I) (i : Cir I N) :
      (∏ j ∈ γ.support, looped r N i j ^ γ j)=(price r γ:ℂ)*hop N i γ := by
    change (γ.prod fun j k => looped r N i j ^ k) = _
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp only [hop,price,looped,mul_pow,prod_mul_distrib,Complex.ofReal_prod,Complex.ofReal_pow]
  simp_rw [load, MvPolynomial.eval_eq, hx, mul_sum]
  rw [sum_comm, sum_eq_single x]
  · let Z := Fintype.card (Cir I N)
    let u := (price r x:ℂ)
    haveI : Nonempty (Fin N) := ⟨⟨0,h⟩⟩
    have hZ : (Z : ℂ)≠0 := by unfold Z; exact_mod_cast Fintype.card_ne_zero
    have hv : u ≠ 0 := by unfold u; exact_mod_cast hp.ne'
    apply Eq.symm
    refine (sum_congr rfl (g:=fun i => (hop N i x)⁻¹*hop N i x*(u⁻¹*(Z:ℂ)⁻¹*u*coeff x p))
      (fun i _ => ?_)).trans ?_
    · change u⁻¹ * _* _ * (_ * (u* _)) = _; ring
    rw [← sum_mul, isolates x x N he he, if_pos rfl]; change (Z:ℂ)*_=_; field_simp
  · intro b hb hu
    refine (sum_congr rfl (g:=fun i => (hop N i x)⁻¹*hop N i b*((price r x:ℂ)⁻¹ *
      (Fintype.card (Cir I N):ℂ)⁻¹ * coeff b p * (price r b:ℂ))) (fun i _ => by ring)).trans ?_
    rw [← sum_mul, isolates x b N he (hh b hb), if_neg (Ne.symm hu),zero_mul]
  intro hh; simp [MvPolynomial.notMem_support_iff.mp hh]

/-- Grid can fit every polynomial on a finite piece at once. -/
lemma span (X : Finset (Grade I)) (x : Grade I) : ∃ N : ℕ, 0<N ∧ (∀ i,x i < N) ∧ ∀ y∈X,∀ i,y i < N := by
  let s := insert x X
  let f (y : Grade I) := ∑ i,y i
  let u := s.sum f
  have h (y : Grade I) (hy : y∈s) (i : I) : y i < u+1 := Nat.lt_succ_of_le (
    (single_le_sum (fun (j:I) _ => Nat.zero_le (y j)) (mem_univ i)).trans
    (single_le_sum (fun j _ => Nat.zero_le (f j)) hy))
  exact ⟨_,Nat.zero_lt_succ _,h _ (mem_insert_self ..),fun i hi => h _ (mem_insert_of_mem hi)⟩
end YM.Multi.Desk
