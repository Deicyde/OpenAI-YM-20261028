import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Loans

/-!
# Local words with full factorial price

Use either the `μ+gZ` convention or already-composed words; `g` is
even allowed to be complex. Smooth probe budgets automatically on these
words. No multiplicity from a distinct anchor a site distance zero away
was suppressed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open Filter Function Set Finset
open YM.Multi.Vacuum.Gauss Probe
open scoped Topology BigOperators
variable {I W : Type} [Fintype I] [DecidableEq I]
namespace Words

def entry (m : I → ℂ) (g : ℂ) (x : Row I) (i : I) := m i+g*(x i : ℂ)

/-- Take a weight ιr in the quadratic bill for each coordinate actually
occurring (not necessarily ONLY the arguments of this word, because must
use same majorant across the polynomial; other argument payments in `w`). -/
def height (ιr : ℝ) (d : ℕ) := Real.sqrt (((d:ℝ)+1)/ιr)

def bulk (ιr : ℝ) (d : ℕ) (M : ℝ) (g : ℂ) := M+‖g‖*height ιr d

lemma height_pos {ιr : ℝ} (hιr : 0 < ιr) (d : ℕ) : 0 < height ιr d := by unfold height; positivity
lemma bulk_nn (ιr : ℝ) (d : ℕ) {M : ℝ} (hM : 0 ≤ M) (g : ℂ) : 0 ≤ bulk ιr d M g := by unfold bulk height; positivity

private lemma up (x L : ℝ) (hL : 0<L) : ‖x‖ ≤ L*Real.exp (x^2/L^2) := by
  rw [Real.norm_eq_abs,mul_comm L,← div_le_iff₀ hL]
  have he := Real.add_one_le_exp (x^2/L^2); have hi : x^2/L^2=(|x|/L)^2 := by rw [div_pow,sq_abs]
  rw [hi] at he ⊢; nlinarith

omit [DecidableEq I] in
lemma value_one (m : I → ℂ) (g : ℂ) {ιr M : ℝ} (d : ℕ) (w : Row I) (hw : ∀ i,0 ≤ w i)
    (i : I) (hιr : 0 < ιr) (he : ιr ≤ w i) (hh : ‖m i‖ ≤ M) (x : Row I) :
    ‖entry m g x i‖ ≤ bulk ιr d M g * Real.exp (pay w x/(d+1)) := by
  let L := height ιr d; let K := Real.exp (pay w x/(d+1))
  have hp := mul_nonneg (show 0 ≤ w i from hw i) (sq_nonneg (x i))
  have hk : 1 ≤ K := Real.one_le_exp (div_nonneg (sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) (by positivity))
  have ht := height_pos hιr d
  have hr : ‖x i‖ ≤ L * K := by
    apply le_trans (up _ L ht)
    apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) ht.le
    rw [show L^2=_ from Real.sq_sqrt (show 0 ≤ (((d:ℝ)+1)/ιr) by positivity), div_div_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [mul_comm]; exact (mul_le_mul_of_nonneg_right he (sq_nonneg _)).trans (single_le_sum (f:=fun i => w i * x i ^2)
       (fun i _ => mul_nonneg (hw i) (sq_nonneg _)) (mem_univ _))
  unfold entry; apply le_trans (norm_add_le ..); rw [norm_mul,Complex.norm_real]
  change _ ≤ (M+‖g‖*L)*K
  rw [add_mul, mul_assoc]; exact add_le_add (hh.trans (le_mul_of_one_le_right ((norm_nonneg _).trans hh) hk))
    (mul_le_mul_of_nonneg_left hr (norm_nonneg _))

variable (m : I → ℂ) (g : ℂ)
omit [DecidableEq I] in
lemma letter_deriv (i : I) (x : Row I) :
    HasFDerivAt (fun x => entry m g x i) (g • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))) x := by
  convert! ((((Complex.ofRealCLM.hasFDerivAt).comp x (hasFDerivAt_apply (𝕜:=ℝ) i x)).const_mul g).const_add
    (m i)) using 1

def verse (s : Finset W) (f : W → I) (x : Row I) := ∏ j∈s,entry m g x (f j)
omit [Fintype I] [DecidableEq I] in
lemma verse_reads (s : Finset W) (f : W → I) (S : Finset I) (h : ∀ i∈s,f i∈S) :
    Reads S (verse m g s f) := by intro x y he; refine prod_congr rfl fun i hi => ?_; unfold entry; rw [he _ (h i hi)]

variable [DecidableEq W]
def note (a i : I) := if i=a then g else 0

lemma solo (s : Finset W) (f : W → I) : Differentiable ℝ (verse m g s f) ∧ ∀ a x,
    hit (verse m g s f) a x= ∑ i∈s, note g a (f i) * verse m g (s.erase i) f x := by
  have he (x : Row I) : HasFDerivAt (verse m g s f) _ x := HasFDerivAt.finsetProd (g:=fun i x => entry m g x (f i))
    (u:=s) (fun i _ => letter_deriv m g _ x)
  refine ⟨fun x => (he x).differentiableAt,fun a x => ?_⟩
  rw [hit,(he x).fderiv, _root_.sum_apply]; apply sum_congr rfl; intro i hi
  simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, basis, Pi.single_apply]
  unfold note; split <;> simp only [Complex.ofReal_one,mul_one,Complex.ofReal_zero, mul_zero,zero_mul]
  exact mul_comm _ _

variable {ιr M : ℝ} (d : ℕ) (w : Row I) (hw : ∀ i,0 ≤ w i) (hιr : 0 < ιr) (hM : 0 ≤ M)

def weight (A : ℝ) (r k : ℕ) := (r.descFactorial k:ℝ) * A ^ (r-k) * ‖g‖^k

include hw hιr hM
omit [DecidableEq I] [DecidableEq W] in
private lemma verse_size (s : Finset W) (f : W → I) (hf : s.card ≤ d)
    (he : ∀ i∈s, ιr ≤ w (f i) ∧ ‖m (f i)‖ ≤ M) (x : Row I) :
    ‖verse m g s f x‖ ≤ bulk ιr d M g ^ s.card * Real.exp (pay w x) := by
  have hK := bulk_nn ιr d hM g
  have hp : 0 ≤ pay w x := sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  apply le_trans (Finset.norm_prod_le ..)
  apply le_trans (prod_le_prod (fun _ _ => norm_nonneg _) (fun i hi => value_one m g d w hw (f i) hιr
    (he i hi).1 (he i hi).2 x))
  rw [prod_const,mul_pow,← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (pow_nonneg hK _)
  have he : (s.card:ℝ)≤d := by exact_mod_cast hf
  rw [← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

lemma price (f : W → I) (n : ℕ) : ∀ (s : Finset W), s.card ≤ d →
    (∀ i∈s, ιr ≤ w (f i) ∧ ‖m (f i)‖ ≤ M) → Costs n (verse m g s f) w (weight g (bulk ιr d M g) s.card) := by
  let B := bulk ιr d M g
  have hc : 0 ≤ B := bulk_nn _ _ hM g
  have hp (s j : ℕ) : 0 ≤ weight g B s j := by unfold weight; positivity
  have he (s : Finset W) (hs : s.card ≤ d) (he : ∀ i∈s, ιr ≤ w (f i) ∧ ‖m (f i)‖ ≤ M) (x) :
      ‖verse m g s f x‖ ≤ weight g B s.card 0 * Real.exp (pay w x) := by
    simpa [weight,B] using verse_size m g d w hw hιr hM s f hs he x
  induction n with
  | zero => intro s hs hf; exact Loan.entry (hp s.card) (solo m g s f).1.continuous (he s hs hf)
  | succ k ih =>
    intro s hs hf
    refine Loan.next (hp s.card) (solo m g s f).1 (he s hs hf) (fun a => ?_)
    rw [show hit (verse m g s f) a=fun x=>_ from funext ((solo m g s f).2 a)]
    have hr i (_hi : i∈s) := Loan.scaling (note g a (f i)) (ih (s.erase i)
      ((Finset.card_le_card (erase_subset ..)).trans hs) (fun j hj=>hf _ (mem_of_mem_erase hj)))
    apply Loan.longer (Loan.batch s _ _ hr); intro r
    -- price of removal for each picked leg with its actual scalar, bounded by full number of choices
    change ∑ i∈s,(‖note g a (f i)‖*weight g B (s.erase i).card r) ≤ weight g B s.card (r+1)
    refine le_trans (b:=∑ _i∈s,(‖g‖*weight g B (s.card-1) r)) (sum_le_sum fun i hi => ?_) ?_
    · rw [card_erase_of_mem hi]; unfold note; split
      · exact le_rfl
      rw [norm_zero,zero_mul]; exact mul_nonneg (norm_nonneg _) (hp _ _)
    rw [sum_const,nsmul_eq_mul, weight,weight]
    cases hj : s.card with
    | zero => simp
    | succ j => rw [Nat.descFactorial_succ,Nat.succ_descFactorial, Nat.cast_mul,pow_succ]; simp only [Nat.add_sub_add_right,Nat.add_sub_cancel_right]; exact Eq.le (by ring)
end Words
end YM.Primitives.GCC
