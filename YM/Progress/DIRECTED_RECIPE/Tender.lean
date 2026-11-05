import YM.Next.SCHEDULE.Dues
import YM.Progress.DIRECTED_RECIPE.EvalBounds

/-!
# Separate transfer costs suffice for Ingredients

The hard populations & taper before fusion may be estimated separately. Show
how to price the actual resources in this recipe, with no volume-dependent
post-usage weakening. Exact (hatted) geometric costs; K required fee strong
enough to leave gamma after inflating by exp of a positive reserve. Useful also
for the proposed startups where the log expansions vary over the full band.

Not the nonlinear producer. Pre data have NO fused/buy stamp assumed, but h/s
bounds here with structural, selection support etc are obligations of that
magnitude; this module just makes it cheaper to pay them from labeled bounds
and numerical Loops. Doesn't infer cover-price compatibility from addressing.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG Lattice Wilson RG.Shoot Ovens Ovens.Pipes
open Next.Scheduling RG.Supply MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

namespace Payments
variable {G : Gauge} {n : Side} {X : Pipes G n} {P : BudgetPoint} {d : Tap G n}
variable {w s a b : ℝ} {p q : ℕ → ℝ}

/-- same numerics as in `Ingredients.pays`. `w` this scale's goal. -/
def inflation (a b κ : ℝ) := Real.exp κ * a + 2*b
structure Rates (B : ℕ) (w a b κ : ℝ) : Prop where
  heading : 0 ≤ κ
  hard : 0 ≤ a
  soft : 0 ≤ b
  soft_limit : b ≤ 1
  capital : (B+B+1:ℕ)^4 * inflation a b κ ≤ (1 : ℝ)
  returns : Bid.quote κ (inflation a b κ) ≤ w

/-- Costs at +1 exponent. -/
def hardCost (P : BudgetPoint) (X : Pipes G n) (p : ℕ → ℝ) (a : ℝ) :=
  (∀ i, 0 ≤ p i) ∧ Ac.Hit (fun i => (X.kernel i).support) P.B p (P.supportExponent+1) a

def softCost (P : BudgetPoint) (X : Pipes G n) (p : ℕ → ℝ) (a : ℝ) :=
  (∀ i, 0 ≤ p i) ∧ Ac.Hit X.softer P.B p (P.supportExponent+1) a

def rooted (d : Tap G n) (p q : ℕ → ℝ) := ∀ i U,
    ‖d.forced i U‖ ≤ p i ∧ ‖d.logarithm i U‖ ≤ q i

-- Use structural/symmetry hypotheses even for vacuum stage
structure Fittings (d : Tap G n) (X : Pipes G n) (P : BudgetPoint) : Prop where
  regular : (X.pours d).RegularFamily P
  support : (X.pours d).ForcedFamily P
  moves : ∀ s b, Nonempty ((X.pours d).Moves s b)
  visits i : ∀ U, d.logarithm i U≠0 → ¬Healthy P.threshold (X.softer i) U
  steady i : GaugeInvariant (d.logarithm i)
  looks i : UsesFinal P.threshold (X.softer i) (d.logarithm i)
  reads i : Measurable (d.logarithm i)
  carries (s : Signed) (b : Site n) : ∃ v : Equiv.Perm ℕ,
    (∀ i, X.softer (v i) = (X.softer i).image (affine s b)) ∧
    ∀ U i, d.logarithm (v i) U=d.logarithm i (pull s b U)

lemma drop_reserve (P : BudgetPoint) (X : ℕ → Support n)
    (hi : ∀ i, 0 ≤ p i) (hp : Ac.Hit X P.B p (P.supportExponent+1) a) :
    ∀ x, SumBudget (fun i => if x∈X i then P.mass (X i) (p i) else 0) a := by
  intro x
  refine Payment.smaller (hp x) (fun i => ?_) (fun i => ?_)
  · split
    · exact (hi i).trans (P.loMass _ _ (hi i))
    exact le_rfl
  split_ifs
  · unfold BudgetPoint.mass; rw [mul_comm (p _)]
    exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right
      (by linarith) (by positivity))) (hi _)
  exact le_rfl

private lemma give (X : ℕ → Support n) (a κ C : ℝ) (f : ℕ → ℝ) (hp : 0 ≤ C) (B : ℕ)
    (h : Ac.Hit X B f a κ) : Ac.Hit X B (fun i => C*f i) a (C*κ) := by
  intro x
  let g i := if x∈X i then f i*Real.exp (a*coverNumber B (X i)) else 0
  have he (i) : (if x∈X i then (C*f i)*Real.exp (a*coverNumber B (X i)) else 0)=C*g i := by
    by_cases hi:x∈X i <;> simp only [hi,g,↓reduceIte,mul_assoc,mul_zero]
  rw [funext he]
  refine ⟨fun i => mul_nonneg hp ((h x).1 i), (h x).2.1.mul_left C,?_⟩
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (h x).2.2 hp

private def blend (p q : ℕ → ℝ) (κ : ℝ) : Label → ℝ := Sum.elim (fun i => Real.exp κ*p i) (fun i => 2*q i)

private lemma blendable (L : Label → ℝ) {a b} (h : SumBudget (L ∘ Sum.inl) a)
    (he : SumBudget (L ∘ Sum.inr) b) : SumBudget L (a+b) := by
  have ht : HasSum L _ := HasSum.sum h.2.1.hasSum he.2.1.hasSum
  refine ⟨fun l => ?_,ht.summable,(ht.tsum_eq).trans_le (add_le_add h.2.2 he.2.2)⟩
  cases l
  · exact h.1 _
  exact he.1 _

private lemma merges (he : hardCost P X p a) (hs : softCost P X q b) (κ : ℝ) :
    (∀ i, 0 ≤ blend p q κ i) ∧ Ac.Hit X.patch P.B (blend p q κ) (P.supportExponent+1) (inflation a b κ) := by
  refine ⟨fun i => ?_, fun x => ?_⟩
  · cases i
    · exact mul_nonneg (Real.exp_nonneg _) (he.1 _)
    exact mul_nonneg (by norm_num) (hs.1 _)
  exact blendable _ (give _ _ _ _ _ (Real.exp_nonneg κ) _ he.2 x)
    (give _ _ _ _ _ (by norm_num : 0 ≤ (2:ℝ)) _ hs.2 x)

private lemma shares (κ : ℝ) (hk : rooted d p q) (hs : softCost P X q b) (hl : b≤1) :
    ∀ i U, |reach d i U| ≤ i.elim (fun _ => Real.exp (-κ)) (fun _ => 1)*blend p q κ i := by
  rintro (i|i) U
  · simp only [reach,Sum.elim_inl,blend,Real.exp_neg, inv_mul_cancel_left₀ (Real.exp_pos κ).ne']
    exact (hk i U).1
  simp only [reach,Sum.elim_inr,one_mul,blend]
  apply (Real.abs_exp_sub_one_le ?_).trans (mul_le_mul_of_nonneg_left (hk i U).2 zero_le_two)
  obtain ⟨x,hx⟩ := X.sites i
  have he := Samples.one_le_quote (drop_reserve P _ hs.1 hs.2 x) i
  rw [if_pos hx] at he
  exact (hk i U).2.trans ((P.loMass _ _ (hs.1 i)).trans (he.trans hl))

private lemma inflates (P : BudgetPoint) {κ : ℝ} (h : Rates P.B w a b κ) :
    0 ≤ inflation a b κ := add_nonneg (mul_nonneg (Real.exp_nonneg _) h.hard) (mul_nonneg zero_le_two h.soft)

/-- Apply to each actually retained point. Fused data then inherit the real
per-anchor bills at P without shrinking e. -/
theorem tender {δ κ : ℝ} (he : Fittings d X P) (hu : (X.pours d).EBound P δ)
    (ha : hardCost P X p a) (hb : softCost P X q b) (hc : rooted d p q)
    (h : Rates P.B w a b κ) : Ingredients X d P δ w := by
  refine ⟨κ,inflation a b κ,a,⟨?_,he.visits,?_,he.steady,he.looks,he.reads,he.carries⟩,?_,h.returns⟩
  · exact ⟨he.regular,he.support,he.moves,hu,p, fun i => ⟨ha.1 i,fun U => (hc i U).1⟩,
      drop_reserve P _ ha.1 ha.2⟩
  · exact ⟨q, Activities.summable_charge X.sites hb.1 (drop_reserve P _ hb.1 hb.2),
      fun i U => (hc i U).2⟩
  have ht := merges ha hb κ
  exact ⟨⟨inflates P h,h.heading,h.capital⟩, _, ht.1, shares κ hc hb h.soft_limit, ht.2⟩


end Payments
end YM.Progress.DirectedRecipe
