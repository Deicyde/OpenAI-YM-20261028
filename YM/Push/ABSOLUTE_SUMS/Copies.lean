import YM.Push.ABSOLUTE_SUMS.Clusters
import YM.Push.ABSOLUTE_SUMS.Distinct


/-!
# Unordered repeats in the merging exponential

In addition to the preceding NUMBERED cluster/forest factorial estimates,
here are estimates for E's other normalization (7612): a product of
inverse repetition factorials in the expansion in missing edges/etc.
Indexing by a set of addresses and a **positive multiplicity** at each;
never count an absent address again. Connectivity/prices on the complete
stencils. Can restrict to selecting compulsory d terms at most once,
test their original internal exclusion, restrict the negative-log
contributors to any tested subset, etc. Factorial paid even as sizes
vary unboundedly. Can charge marks per copy for extracting at forced
components.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Multiple
open Trees RG Ursell Finset Lattice
open scoped BigOperators Classical Topology
variable {n : Side} {ι : Type*}

abbrev Reps (ι : Type*) := Σ s : Finset ι, (↥s → ℕ)

def manyW (w : ι → ℝ) (r : Reps ι) :=
    ∏ i : ↥r.1, w i.val^(r.2 i+1) / (r.2 i+1).factorial

def card (r : Reps ι) := ∑ i : ↥r.1, (r.2 i+1)

def tally (f : ι → ℝ) (r : Reps ι) := ∑ i : ↥r.1, (r.2 i+1:ℕ)*f i.val

lemma manyW_nonneg {w : ι → ℝ} (hw : ∀ i,0 ≤ w i) (r : Reps ι) :
    0 ≤ manyW w r := prod_nonneg fun _ _ => div_nonneg (pow_nonneg (hw _) _) (by positivity)

lemma tally_scale (w e : ι → ℝ) (r : Reps ι) :
    manyW (fun i => w i*Real.exp (e i)) r = manyW w r * Real.exp (tally e r) := by
  unfold manyW tally; rw [Real.exp_sum,← prod_mul_distrib]; apply prod_congr rfl; intro i _
  rw [Real.exp_nat_mul,mul_pow]; ring

lemma card_scale (c : ℝ) (w : ι → ℝ) (r : Reps ι) :
    manyW (fun i => c*w i) r = manyW w r * c^(card r) := by
  unfold manyW card; rw [← Finset.prod_pow_eq_pow_sum,← prod_mul_distrib]; apply prod_congr rfl; intro i _
  rw [mul_pow]; ring

private lemma product_sum {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℕ → ℝ) (c : α → ℝ)
    (hw : ∀ i, SumBudget (w i) (c i)) : SumBudget (fun z : α → ℕ => ∏ i, w i (z i)) (∏ i, c i) := by
  let f := fun z : Unit × (α → ℕ) => ∏ i, w i (z.2 i)
  have hp i : 0 ≤ f i := prod_nonneg fun j _ => (hw j).1 _
  have H : SumBudget f (∏ i,c i) := budget_assignments f hp (fun D => by
    simp only [Fintype.sum_unique,f]; rw [← Fintype.prod_sum (fun (i:α) (x : D) => w i x.val)]
    apply prod_le_prod (fun i _ => sum_nonneg fun _ _ => (hw i).1 _)
    intro i _; rw [← Finset.sum_subtype D (p:=(·∈D)) (fun i => Iff.rfl) (w i)]
    exact budget_sum (hw i) D)
  exact budget_pull (fun z : α → ℕ => ((),z)) (fun i j e => congr_arg Prod.snd e) H

/-- A convenient overestimate at each distinct-vertex set. -/
lemma buy_at (s : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {σ : ℝ} (h1 : 0 ≤ σ) (h2 : σ < 1)
    (ht : ∀ i∈s, w i ≤ σ) : SumBudget (fun z => manyW w ⟨s,z⟩)
    (∏ i∈s, w i*(1-σ)⁻¹) := by
  rw [Finset.prod_subtype s (p:=(·∈s)) (fun _ => Iff.rfl)]
  apply product_sum (fun (i:↥s) (k : ℕ) => w i.val^(k+1)/(k+1).factorial)
    (fun (i:↥s) => w i.val*(1-σ)⁻¹)
  intro i; have he := hw i.val; have hh := ht _ i.property
  apply budget_mono (budget_geometric he h1 h2)
  · intro i; positivity
  intro k
  have hv : 1 ≤ ((k+1).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos (k+1)
  exact (div_le_self (by positivity) hv).trans ((pow_succ' _ _).trans_le
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he hh _) he))

variable (X : ι → Support n) (M : ℕ)

def connected (x : Site n) (w : ι → ℝ) (r : Reps ι) :=
    if Ac.Spark X r.1 ∧ x∈r.1.biUnion X then manyW w r else 0

private lemma paid (x : Site n) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hn : ∀ i, (X i).Nonempty)
    {a γ δ q σ : ℝ} (h1 : 0 ≤ σ) (h2 : σ < 1) (h : Ready X M (fun i => w i * (1-σ)⁻¹) a γ δ q)
    (hh : γ ≤ σ) : SumBudget (connected X x (charge X M w a)) (γ*(1-q)⁻¹) := by
  let u := fun i => w i*(1-σ)⁻¹
  let v := charge X M w a
  let f := fun s : Finset ι => touches X M u a x s
  have hk : SumBudget f (γ*(1-q)⁻¹) := by
    simpa only [f,u,Nat.zero_le,↓reduceIte,mul_one,pow_zero] using touch_tail X M h x 0
  have hv : (∀ i, 0 ≤ v i) := charge_pos _ _ hw _
  have hD : 0<(1-σ) := by linarith
  have hh i : v i ≤ σ := by
    obtain ⟨z,hz⟩ := hn i
    have ht := budget_single (test_hit X M h z) i
    rw [currency_add,hit,if_pos hz] at ht
    refine le_trans ?_ (ht.trans hh)
    calc
      v i ≤ v i * ((1-σ)⁻¹ * currency M δ (X i)) := by
        apply le_mul_of_one_le_right (hv i)
        have hj : 1 ≤ currency M δ (X i) := Real.one_le_exp (mul_nonneg h.2.1.le (by positivity))
        have hy : 1 ≤ (1-σ)⁻¹ := (one_le_inv₀ hD).mpr (by linarith)
        exact one_le_mul_of_one_le_of_one_le hy hj
      _ = _ := by unfold v charge; ring
  apply sigma_total (connected X x v) f _ hk
  intro k; by_cases hl : Ac.Spark X k ∧ x∈k.biUnion X
  · simp only [connected,touches,hl,f]
    apply budget_loosen (buy_at k v hv h1 h2 fun i _ => hh i)
    apply le_of_eq; apply prod_congr rfl; intro i _; unfold v charge u; ring
  simp only [connected,touches,hl,f,if_false]
  apply budget_of_sum (fun _ => le_rfl) (by simp)

lemma cover_pay (r : Reps ι) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (x : Site n) {a : ℝ}
    (ha : 0 ≤ a) : currency M a (r.1.biUnion X) * connected X x w r ≤
    connected X x (charge X M w a) r := by
  unfold connected; split
  next he =>
    let v i := a*(coverNumber M (X i):ℝ)
    change _ ≤ manyW (fun i => w i * Real.exp (v i)) r
    rw [tally_scale,mul_comm]
    apply mul_le_mul_of_nonneg_left _ (manyW_nonneg hw r)
    apply Real.exp_monotone
    calc
      _ ≤ a*((∑ i∈r.1,coverNumber M (X i):ℕ):ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast Ac.cover X M he.1) ha
      _ = ∑ i∈r.1,v i := by rw [Nat.cast_sum,mul_sum]
      _ ≤ _ := by
        unfold tally; rw [Finset.sum_subtype r.1 (p:=(·∈r.1)) (fun _ => Iff.rfl) v]
        apply sum_le_sum; intro i _; exact le_mul_of_one_le_left
          (mul_nonneg ha (by positivity)) (by exact_mod_cast (show 1 ≤ _+1 from Nat.le_add_left 1 _))
  next he => simp

/-- Normalized multiset sum, retaining exponential cover price on its
connected footprint, and a geometric tail. Q e.g. contains at least
one d-type occurrence, then can extract a mark. Take t>1 for decay.
May drop any terms coexisting on earlier geometries for an upper bound,
no independence needed or inferred. If there are unrooted empty-support
labels, use separate prices; here assume actual label style nonempty. -/
theorem estimates (w e : ι → ℝ) (x : Site n) (hw : ∀ i,0 ≤ w i) (hn : ∀ i,(X i).Nonempty)
    {a γ δ q σ t : ℝ} (ha : 0 ≤ a) (ht : 1 ≤ t) (h1 : 0 ≤ σ) (h2 : σ < 1)
    (h : Ready X M (fun i => (t*(w i*Real.exp (e i))) * (1-σ)⁻¹) a γ δ q) (hh : γ ≤ σ)
    (Q : Reps ι → Prop) [DecidablePred Q] {v : ℝ} (he : ∀ r, Q r → v ≤ tally e r) (m : ℕ) :
    SumBudget (fun r => if Q r ∧ m ≤ Multiple.card r then currency M a (r.1.biUnion X)*connected X x w r else 0)
      (((t^m)⁻¹ * Real.exp (-v))*(γ*(1-q)⁻¹)) := by
  have ht' : 0 < t := zero_lt_one.trans_le ht
  let W := fun i => (t*(w i*Real.exp (e i)))
  have hW i : 0 ≤ W i := mul_nonneg ht'.le (mul_nonneg (hw i) (Real.exp_pos _).le)
  let P := (t^m)⁻¹ * Real.exp (-v)
  have hp : 0 ≤ P := by unfold P; positivity
  have hg w' r (hw : ∀ i,0 ≤ w' i) : 0 ≤ connected X x w' r := by
    unfold connected; split <;> first | exact manyW_nonneg hw _ | exact le_rfl
  refine budget_mono (budget_scale hp (paid X M x hW hn h1 h2 h hh)) (fun r => ?_)
    (fun r => ?_)
  · split <;> first | exact mul_nonneg (Real.exp_pos _).le (hg w r hw) | exact le_rfl
  split
  next hv =>
    calc
      _ ≤ P * (currency M a (r.1.biUnion X)*connected X x W r) := by
        rw [mul_left_comm P]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        unfold connected; split
        next hy =>
          unfold W; rw [card_scale,tally_scale]
          rw [show P*(manyW w r*Real.exp _ * t^Multiple.card r) = manyW w r*(P*(t^Multiple.card r*Real.exp (tally e r))) by ring]
          have hc : t^m ≤ t^(Multiple.card r) := pow_le_pow_right₀ ht hv.2
          apply le_mul_of_one_le_right (manyW_nonneg hw _)
          have hV : Real.exp v ≤ Real.exp (tally e r) := Real.exp_monotone (he _ hv.1)
          calc
            (1:ℝ) = P*(t^m*Real.exp v) := by unfold P; rw [Real.exp_neg]; have he := Real.exp_pos v; field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hc hV (Real.exp_pos _).le (by positivity)) hp
        next hy => simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (cover_pay X M r hW x ha) hp
  next hv => exact mul_nonneg hp (hg _ r (charge_pos X M hW a))
end YM.Push.AbsoluteSums.Multiple
