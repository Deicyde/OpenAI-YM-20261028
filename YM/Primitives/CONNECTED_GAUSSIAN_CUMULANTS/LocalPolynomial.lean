import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Word

/-!
# Compile actual complex local polynomials to the ordered probe class

Includes sold ℓ¹/factorial costs without term cancellation. Use small
per-stencil weights as chosen by the caller. Homogeneous or valuation users
may retain the individual entries before rebinning, e.g., there's no floor of
one on the basic bulk factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open Function Finset MvPolynomial
open YM.Multi.Vacuum.Gauss Probe Words
open scoped Topology BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]
namespace LocalPolynomial

abbrev Script (I : Type) := MvPolynomial I ℂ
abbrev Order (I : Type) := I →₀ ℕ

def placed (m : I → ℂ) (g : ℂ) (v : Script I) (x : Row I) : ℂ := MvPolynomial.aeval (entry m g x) v

def markedOn (v : Script I) (S : Finset I) := ∀ s∈v.support,s.support⊆S

abbrev Key (s : Order I) := Σ i : I, Fin (s i)

def length (s : Order I) := s.sum fun _ e => e
omit [DecidableEq I] in
lemma key_length (s : Order I) : (Finset.univ : Finset (Key s)).card=length s := by
  rw [card_univ,Fintype.card_sigma,length,Finsupp.sum_fintype]; rotate_left
  · intro; rfl
  simp only [Fintype.card_fin]

variable (m : I → ℂ) (g : ℂ)
omit [DecidableEq I] in
lemma over (s : Order I) (r : ℂ) (x) : placed m g (monomial s r) x =
    r * verse m g (Finset.univ : Finset (Key s)) Sigma.fst x := by
  unfold placed; rw [aeval_monomial,Finsupp.prod_fintype s _ (by intro; exact pow_zero _),verse,Fintype.prod_sigma]
  simp

omit [DecidableEq I] in
lemma exact_formula (v : Script I) (x) : placed m g v x=
    ∑ s∈v.support,coeff s v * verse m g (Finset.univ : Finset (Key s)) Sigma.fst x := by
  unfold placed; nth_rw 1 [as_sum v]; rw [map_sum]; refine sum_congr rfl fun s _ => ?_; exact over ..

omit [DecidableEq I] in
lemma covered {v : Script I} {S} (h : markedOn v S) : Reads S (placed m g v) := by
  intro x y he; simp_rw [exact_formula]; refine sum_congr rfl fun s hs => ?_
  let f := @Sigma.fst I fun i => Fin (s i)
  congr 1; apply verse_reads m g _ f S (fun i _ => ?_) he
  exact h s hs (Finsupp.mem_support_iff.mpr (by have hi := i.snd.isLt; unfold f; omega))

/-- `cap` bounds even rescaled fields with common scalar g. -/
def cap (v : Script I) (r : ℝ) (d : ℕ) (M : ℝ) (k : ℕ) :=
    ∑ s∈v.support,‖coeff s v‖ * weight g (bulk r d M g) (length s) k

theorem produce (v : Script I) (n d : ℕ) (hd : v.totalDegree ≤ d) (S : Finset I) (h : markedOn v S)
    (w : Row I) (hw : ∀ i,0 ≤ w i) (r M : ℝ) (hr : 0<r) (hM : 0 ≤ M) (he : ∀ i∈S,r ≤ w i ∧ ‖m i‖ ≤ M) :
    Reads S (placed m g v) ∧ Costs n (placed m g v) w (cap g v r d M) := by
  refine ⟨covered m g h,?_⟩
  rw [funext (exact_formula m g v)]; apply Loan.batch
  intro s hs; apply Loan.scaling; rw [← key_length]
  apply Words.price m g d w hw hr hM
  · rw [key_length]; exact (le_totalDegree hs).trans hd
  intro i hi
  exact he _ (h _ hs (Finsupp.mem_support_iff.mpr (by have hh:=i.2.isLt; omega)))

/-- Sup coefficient fee when forgetting the individual factorials. -/
def lump (v : Script I) (r : ℝ) (d : ℕ) (M : ℝ) :=
  (∑ s∈v.support,‖coeff s v‖) * d.factorial * (max 1 (bulk r d M g))^d
omit [Fintype I] [DecidableEq I] in
lemma lump_nn (v : Script I) (r : ℝ) (d : ℕ) (M : ℝ) : 0 ≤ lump g v r d M := by unfold lump; positivity
omit [Fintype I] [DecidableEq I] in
lemma pile (v : Script I) (k d : ℕ) (hd : v.totalDegree≤d) (r M : ℝ) (hM : 0≤M) :
    cap g v r d M k ≤ lump g v r d M*‖g‖^k := by
  let B := max 1 (bulk r d M g)
  have he : 1 ≤ B := le_max_left ..
  have hx : 0 ≤ bulk r d M g := bulk_nn _ _ hM g
  have ht : d.descFactorial k ≤ d.factorial := by
    by_cases he : k ≤ d
    · rw [Nat.descFactorial_eq_div he]; exact Nat.div_le_self ..
    rw [Nat.descFactorial_of_lt (Nat.lt_of_not_ge he)]
    exact Nat.zero_le _
  unfold cap lump; simp_rw [Finset.sum_mul]; refine sum_le_sum fun s hs => ?_
  have hl : length s ≤ d := (le_totalDegree hs).trans hd
  have hb : bulk r d M g ^ (length s-k) ≤ B^d := (pow_le_pow_left₀ hx (le_max_right ..) _).trans (pow_le_pow_right₀ he (by omega))
  have hh : (((length s).descFactorial k):ℝ) ≤ d.factorial := Nat.cast_le.mpr ((Nat.descFactorial_le k hl).trans ht)
  unfold weight
  simp only [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul hh (mul_le_mul_of_nonneg_right hb (by positivity)) (by positivity) (by positivity)) (norm_nonneg _)
end LocalPolynomial
end YM.Primitives.GCC
