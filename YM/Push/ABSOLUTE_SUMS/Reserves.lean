import YM.Push.ABSOLUTE_SUMS.Clusters
import YM.Push.ABSOLUTE_SUMS.Distinct


/-!
# Cover-reserve and marked estimates

Handles the polynomial on the WHOLE component/cluster (cf.

Explicit inequalities charge reserves
on constituents.

Can also specialize to the total cover-price tail
or to many packet-count weights (e.g. put additional mandatory-seed
costs in `extra`).

No limit of normed activities used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Reserves
open RG Lattice Trees Ursell Finset
open scoped Topology BigOperators Classical

variable {n : Side} {ι : Type*}

def polyPrice (ε : ℝ) (k : ℕ) := ε⁻¹^k * k.factorial * Real.exp ε

def extract (ε : ℝ) (k : ℕ) (T U : ℝ) := polyPrice ε k * Real.exp (-ε*T-U)

/-- Simultaneously recover arbitrary-order polynomial in D, a price tail
and mark gains (possibly using several mark radii: put the log of the
product in E). Need the input reserve. -/
lemma reserve_tail (f D E : ι → ℝ) (hf : ∀ i,0 ≤ f i) (hd : ∀ i,0 ≤ D i) {ε c : ℝ}
    (he : 0 < ε) (hb : SumBudget (fun i => f i*Real.exp (2*ε*D i+E i)) c) (k : ℕ)
    (Q : ι → Prop) [DecidablePred Q] {T U : ℝ} (hq : ∀ i, f i≠0 → Q i → T ≤ D i ∧ U ≤ E i) :
    SumBudget (fun i => if Q i then f i*(1+D i)^k else 0) (extract ε k T U * c) := by
  have h (i : ι) : 0 ≤ (1+D i)^k := pow_nonneg (by linarith [hd i]) _
  have ht : 0 ≤ extract ε k T U := by unfold extract polyPrice; positivity
  apply budget_mono (budget_scale ht hb)
  · intro i; split <;> first | exact mul_nonneg (hf i) (h i) | exact le_rfl
  intro i; split
  next hg =>
    by_cases hi : f i=0
    · simp only [hi,zero_mul,mul_zero,le_refl]
    obtain ⟨hl,hp⟩ := hq i hi hg
    calc
      _ ≤ f i*(polyPrice ε k*Real.exp (ε*D i)) :=
        mul_le_mul_of_nonneg_left (polynomial_cost he (hd i) k) (hf i)
      _ ≤ f i*(polyPrice ε k*(Real.exp (-ε*T-U)*Real.exp (2*ε*D i+E i))) := by
        apply mul_le_mul_of_nonneg_left _ (hf i)
        have hg : 0 ≤ polyPrice ε k := by unfold polyPrice; positivity
        rw [← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hg
        apply Real.exp_monotone; nlinarith
      _ = _ := by unfold extract; ring
  next hg => exact mul_nonneg ht (hb.1 _)

-- Price definitions. `mark` can be zero.
def tariff (w extra mark : ι → ℝ) (ε : ℝ) (i : ι) := w i * Real.exp (2*ε*extra i + mark i)
def weight (X : ι → Support n) (B : ℕ) (extra : ι → ℝ) (i : ι) := (coverNumber B (X i):ℝ)+extra i

section GlobalCost
variable (X : ι → Support n) (B : ℕ) (w extra mark : ι → ℝ) (ε a : ℝ)

lemma exchange (i : ι) : charge X B (tariff w extra mark ε) (a+2*ε) i = charge X B w a i *
    Real.exp (2*ε*weight X B extra i + mark i) := by
  unfold charge currency tariff weight; simp only [mul_assoc,← Real.exp_add]; ring_nf

lemma set_exchange (x : Site n) (s : Finset ι) :
    touches X B (tariff w extra mark ε) (a+2*ε) x s = touches X B w a x s *
      Real.exp (2*ε*(∑ i∈s, weight X B extra i) + ∑ i∈s, mark i) := by
  unfold touches; split
  next he =>
    rw [Finset.mul_sum,← Finset.sum_add_distrib,Real.exp_sum]
    change (∏ i∈s,charge X B (tariff w extra mark ε) (a+2*ε) i) =
      (∏ i∈s,charge X B w a i)*_
    simp_rw [exchange,Finset.prod_mul_distrib]
  next he => rw [zero_mul]

lemma tuple_exchange (R : ι → ι → Prop) (m : ℕ) (z : Tuple ι m) :
    clusters R (charge X B (tariff w extra mark ε) (a+2*ε)) z = clusters R (charge X B w a) z *
      Real.exp (2*ε*(∑ i, weight X B extra (z i)) + ∑ i, mark (z i)) := by
  unfold clusters; rw [Finset.mul_sum,← Finset.sum_add_distrib,Real.exp_sum]; simp_rw [exchange,
    Finset.prod_mul_distrib]; ring
end GlobalCost

section Weighted
variable (X : ι → Support n) (B : ℕ) (w extra mark : ι → ℝ)

def rooted (x : Site n) (a : ℝ) (s : Finset ι) : ℝ :=
    if Ac.Spark X s ∧ x∈s.biUnion X then (∏ i∈s, w i)*Trees.currency B a (s.biUnion X) else 0

def setPrice (s : Finset ι) : ℝ := ∑ i∈s, weight X B extra i

def treeYield (γ q : ℝ) (m : ℕ) := γ*q^m*(1-q)⁻¹

theorem sets (hw : ∀ i,0 ≤ w i) (hp : ∀ i,0 ≤ extra i) {ε a γ δ q : ℝ}
    (he : 0 < ε) (ha : 0 ≤ a) (h : Ready X B (tariff w extra mark ε) (a+2*ε) γ δ q)
    (m k : ℕ) (x : Site n) (Q : Finset ι → Prop) [DecidablePred Q] {T U : ℝ}
    (hq : ∀ s : Finset ι, m ≤ s.card-1 → Ac.Spark X s → x∈s.biUnion X → Q s →
      T ≤ setPrice X B extra s ∧ U ≤ ∑ i∈s, mark i) : SumBudget
      (fun s => if Q s ∧ m ≤ s.card-1 then rooted X B w x a s * (1+setPrice X B extra s)^k else 0)
      (extract ε k T U * treeYield γ q m) := by
  have hd (s : Finset ι) : 0 ≤ setPrice X B extra s := Finset.sum_nonneg fun i _ =>
    add_nonneg (Nat.cast_nonneg _) (hp i)
  let f (s : Finset ι) := if m ≤ s.card-1 then rooted X B w x a s else 0
  have hg i : 0 ≤ rooted X B w x a i := by
    unfold rooted; split <;> first | exact le_rfl | exact mul_nonneg (prod_nonneg fun i _ => hw _) (Real.exp_pos _).le
  have hf i : 0 ≤ f i := by unfold f; split <;> first | exact le_rfl | exact hg _
  let D := setPrice X B extra
  let E := fun s : Finset ι => ∑ i∈s, mark i
  have H : SumBudget (fun i => f i * Real.exp (2*ε*D i + E i)) (treeYield γ q m) := by
    refine budget_mono (touch_tail X B h x m) (fun i => mul_nonneg (hf i) (Real.exp_pos _).le)
      fun i => ?_
    unfold f; split
    next hi =>
      rw [set_exchange]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      unfold rooted touches; split
      next he =>
        unfold currency
        simp only [Finset.prod_mul_distrib,← Real.exp_sum,← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left
          (by exact_mod_cast Ac.cover X B he.1) ha)) (prod_nonneg fun i _ => hw _)
      next he => exact le_rfl
    next hi => rw [zero_mul]
  have hb (i : Finset ι) (hh : f i≠0) (hz : Q i) : T ≤ D i ∧ U ≤ E i := by
    unfold f rooted at hh
    split at hh
    next hi => split at hh
               next he => exact hq i hi he.1 he.2 hz
               next he => contradiction
    next hi => contradiction
  have hk := reserve_tail f D E hf hd he H k Q hb
  convert hk using 1; ext i
  by_cases hl : Q i <;> by_cases he : m ≤ i.card-1 <;> simp [hl, he, f, D]

-- second graph series

def clusterPrice (z : Clusters ι) := ∑ i, weight X B extra (z.2 i)

def occurrence (R : ι → ι → Prop) (a : ℝ) (x : Site n) (z : Clusters ι) := if x∈unionOf X z.2 then
      clusters R w z.2 * currency B a (unionOf X z.2) else 0

theorem cluster_prices (R : ι → ι → Prop) (ht : Tests R X) (hw : ∀ i,0 ≤ w i)
    (hp : ∀ i,0 ≤ extra i) {ε a γ δ q : ℝ} (he : 0 < ε) (ha : 0 ≤ a)
    (h : Ready X B (tariff w extra mark ε) (a+2*ε) γ δ q)
    (m k : ℕ) (x : Site n) (Q : Clusters ι → Prop) [DecidablePred Q] {T U : ℝ}
    (hq : ∀ s : Clusters ι, m ≤ s.1 → coefficient R s.2 ≠ 0 → x∈unionOf X s.2 → Q s →
      T ≤ clusterPrice X B extra s ∧ U ≤ ∑ i, mark (s.2 i)) : SumBudget
      (fun s => if Q s ∧ m ≤ s.1 then occurrence X B w R a x s * (1+clusterPrice X B extra s)^k else 0)
      (extract ε k T U * treeYield γ q m) := by
  let W := tariff w extra mark ε; let A := a+2*ε; let p i := x∈X i
  have hr : SumBudget (charge X B (marked p W) (A+δ)) γ := by
    convert h.2.2.2.2.2 x using 1; ext i
    by_cases he : x∈X i <;> simp [charge,marked,p,he,currency,W,A]
  let D := clusterPrice X B extra
  let E := fun s : Clusters ι => ∑ i, mark (s.2 i)
  have hd s : 0 ≤ D s := Finset.sum_nonneg fun i _ => add_nonneg (Nat.cast_nonneg _) (hp _)
  let f (s : Clusters ι) := if m ≤ s.1 then occurrence X B w R a x s else 0
  have hf i : 0 ≤ f i := by
    unfold f occurrence; split
    next he => split
               · exact mul_nonneg (clusters_nonneg R hw _) (Real.exp_pos _).le
               · exact le_rfl
    next he => exact le_rfl
  have H : SumBudget (fun i => f i * Real.exp (2*ε*D i + E i)) (treeYield γ q m) := by
    have hh := cluster_tail R X B ht p h hr m
    refine budget_mono hh (fun i => mul_nonneg (hf i) (Real.exp_pos _).le) fun s => ?_
    change f s * _ ≤ (fun i => _) s
    by_cases hl : m ≤ s.1 ∧ x∈unionOf X s.2
    · obtain ⟨i,-,hi⟩ := mem_biUnion.mp hl.2
      have he' : ∃ i, p (s.2 i) := ⟨i,hi⟩
      unfold f occurrence
      rw [if_pos hl.1,if_pos hl.2]; dsimp only
      rw [if_pos hl.1,if_pos he',tuple_exchange]
      exact mul_le_mul_of_nonneg_right (pay_cover R X B ht hw ha _) (Real.exp_pos _).le
    have he : f s=0 := by
      unfold f occurrence; split
      next he => rw [if_neg (fun hz => hl ⟨he,hz⟩)]
      next he => rfl
    rw [he,zero_mul]; exact hh.1 s
  have hb i (h : f i ≠ 0) (hk : Q i) : T ≤ D i ∧ U ≤ E i := by
    unfold f occurrence at h; split at h
    next he =>
      split at h
      next he' =>
        apply hq i he _ he' hk; rintro hh; simp only [clusters,hh,abs_zero,zero_mul,zero_div,
          ne_eq,not_true_eq_false] at h
      next he' => contradiction
    next he => contradiction
  convert reserve_tail f D E hf hd he H k Q hb using 1
  ext i
  by_cases hl : Q i <;> by_cases he : m ≤ i.1 <;> simp [hl,he,f,D]
end Weighted
end YM.Push.AbsoluteSums.Reserves
