import YM.Ac.Tree
import YM.Push.ABSOLUTE_SUMS.Animals
import YM.Push.ABSOLUTE_SUMS.Parent


/-!
# Overlap-tree estimates (I)

Here per-size receipts.

All supports/prices on the actual periodic
lattice.

Alternative combinatorial proof.

Our named sufficient inequality
for the geometric tail asks `4 γ (B+B+1)^4 / δ < 1` using exponent
reserve `δ > 0`.

(No claim this is necessary.) The larger entropy
constant with respect to degree is harmless if the scheduling estimates
pay this slightly stronger smallness threshold.

`Ac.Hit` is a hypothesis
on individual VERTEX labels, up to their multiplicities; see packet
producer, and the needed estimates for the optional population.

Forest roots below attach to an EXTERNAL support Y. Include n=0 and Y
empty. For root-hit clusters, take Y the footprint of a distinguished
root occurrence and attach all other occurrences by such a forest.
Factorial is that of number of OTHER vertices then. In both cases
all vertices are numbered and any repeats of labels on them are
still counted, including repeats on adjacent vertices. Full tuples and
trees are summed, not evaluating a formal `exp` ignoring that issue.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Trees
open Lattice Finset RG Animals
open scoped Topology BigOperators Classical

variable {n : Side} {ι : Type*} (X : ι → Support n) (B : ℕ)

/-- Set coefficient weight, also applies to winding supports. -/
def currency (B : ℕ) (a : ℝ) (Y : Support n) := Real.exp (a * coverNumber B Y)

def overlapWeight (w : ι → ℝ) (a : ℝ) (Y : Support n) (i : ι) :=
    if Ac.meets X i Y then w i * currency B a (X i) else 0

def stretch (γ δ : ℝ) := (ballCost B:ℝ) * γ / δ

def degreePrice (γ δ : ℝ) := 4 * stretch B γ δ

def fanPrice (δ : ℝ) (Y : Support n) : ℝ := max (δ * coverNumber B Y) 1

lemma overlap_sum {w : ι → ℝ} {a γ : ℝ} (hh : Ac.Hit X B w a γ) (Y : Support n) (D : Finset ι) :
    ∑ i ∈ D, overlapWeight X B w a Y i ≤ Y.card*γ := by
  simpa only [Ac.buds,Finset.sum_filter,currency,overlapWeight] using Ac.demand X B hh Y D

lemma overlap_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a : ℝ) (Y : Support n) (i : ι) :
    0 ≤ overlapWeight X B w a Y i := by
  unfold overlapWeight; split
  · exact mul_nonneg (hw _) (Real.exp_pos _).le
  exact le_rfl

lemma stretch_pos {γ δ : ℝ} (hk : 0 < γ) (hd : 0 < δ) : 0 < stretch B γ δ := by
  unfold stretch; have h := neighbors_ge B; positivity

lemma fanPrice_pos (Y : Support n) (δ : ℝ) : 0 < fanPrice B δ Y := by unfold fanPrice; positivity

private lemma pays_fan (Y : Support n) {δ : ℝ} (hd : 0 < δ) (k : ℕ) :
    fanPrice B δ Y ^ k ≤ (k.factorial:ℝ) * currency B δ Y := by
  let x : ℝ := δ * coverNumber B Y
  have hx : 0 ≤ x := by unfold x; positivity
  have he : 1 ≤ (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
  change (max x 1)^k ≤ _ * Real.exp x
  rcases le_total 1 x with h|h
  · rw [max_eq_left h]
    have hk := (div_le_iff₀ (show 0 < (k.factorial:ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp _ hx k)
    rwa [mul_comm]
  rw [max_eq_right h,one_pow]
  exact he.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp hx))

/-- The support at the parent of `i`. -/
def installed {α : Type*} (Y : Support n) (z : α → ι) : Option α → Support n :=
    label Y (X ∘ z)

def Sprouts {α : Type*} (Y : Support n) (p : α → Option α) (z : α → ι) : Prop :=
    Ranked p ∧ ∀ i, Ac.meets X (z i) (installed X Y z (p i))

/-- Weight for one numbered forest, with parent-map and full labels. -/
def forestWeight {α : Type*} [Fintype α] (w : ι → ℝ) (a : ℝ)
    (Y : Support n) (p : α → Option α) (z : α → ι) : ℝ :=
    if Sprouts X Y p z then (∏ i, (w (z i)*currency B a (X (z i)))) / (Fintype.card α).factorial else 0

lemma forest_nonneg {α : Type*} [Fintype α] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a : ℝ)
    (Y : Support n) (p : α → Option α) (z : α → ι) :
    0 ≤ forestWeight X B w a Y p z := by
  unfold forestWeight; split
  · exact div_nonneg (prod_nonneg fun i _ => mul_nonneg (hw _) (Real.exp_pos _).le) (by positivity)
  exact le_rfl

private lemma overlap_eq {α : Type*} [Fintype α] (w : ι → ℝ) (a : ℝ)
    (Y : Support n) (p : α → Option α) (z : α → ι) (h : Ranked p) :
    forestWeight X B w a Y p z = (∏ i, overlapWeight X B w a (installed X Y z (p i)) (z i)) /
      (Fintype.card α).factorial := by
  unfold forestWeight; split
  next he =>
    congr 1
    exact prod_congr rfl (fun i _ => (if_pos (he.2 i)).symm)
  next he =>
    simp only [Sprouts,h,true_and,not_forall] at he
    obtain ⟨i,hi⟩ := he
    rw [prod_eq_zero (mem_univ i) (show overlapWeight X B w a (installed X Y z (p i)) (z i) = 0 from
      if_neg hi), zero_div]

private lemma prod_fanPrice {α : Type*} [Fintype α] [DecidableEq α] {δ : ℝ} (hd : 0 < δ)
    (Y : Support n) (p : α → Option α) (z : α → ι) :
    (∏ i, fanPrice B δ (installed X Y z (p i))) ≤ (fanout p:ℝ) * (currency B δ Y *
      ∏ i : α, currency B δ (X (z i))) := by
  let c i := installed X Y z i
  calc
    _ = ∏ i : Option α, fanPrice B δ (c i) ^ children p i := by
      have he := prod_fiberwise univ p (fun j => fanPrice B δ (c (p j)))
      apply he.symm.trans
      apply prod_congr rfl; intro i _
      calc
        _ = ∏ _j ∈ univ with p _j=i, fanPrice B δ (c i) := prod_congr rfl fun j hj => by
          rw [(mem_filter.mp hj).2]
        _ = _ := Finset.prod_const _
    _ ≤ ∏ i : Option α, ((children p i).factorial:ℝ) * currency B δ (c i) :=
      prod_le_prod (fun i _ => pow_nonneg (fanPrice_pos B (c i) δ).le _) fun i _ => pays_fan B _ hd _
    _ = _ := by
      rw [prod_mul_distrib,fanout,Nat.cast_prod,Fintype.prod_option (fun i => currency B δ (c i))]; rfl

-- Transition kernels for the proof: with extra exponent and normalized.
private def kernel (w : ι → ℝ) (a γ δ : ℝ) (Y : Support n) (i : ι) :=
    overlapWeight X B w (a+δ) Y i / (stretch B γ δ * fanPrice B δ Y)

private lemma kernel_sum {w : ι → ℝ} {a γ δ : ℝ} (hg : 0 < γ) (hd : 0 < δ)
    (hh : Ac.Hit X B w (a+δ) γ) (Y : Support n) (D : Finset ι) :
    ∑ i ∈ D, kernel X B w a γ δ Y i ≤ 1 := by
  have ho := stretch_pos B hg hd; have hm := fanPrice_pos B Y δ
  let c : ℝ := coverNumber B Y
  have hy : (Y.card:ℝ) ≤ (ballCost B:ℝ) * c := by
    rw [mul_comm]; unfold c ballCost; exact_mod_cast Lattice.Corona.pays Y B
  unfold kernel; rw [← sum_div,div_le_one (by positivity)]
  apply (overlap_sum X B hh Y D).trans
  calc
    _ ≤ ((ballCost B:ℝ) * c)*γ := mul_le_mul_of_nonneg_right hy hg.le
    _ = stretch B γ δ * (δ * c) := by unfold stretch; field_simp
    _ ≤ stretch B γ δ * fanPrice B δ Y := mul_le_mul_of_nonneg_left (le_max_left ..) ho.le

private lemma kernel_pos {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {γ δ : ℝ} (hg : 0 < γ) (hd : 0 < δ)
    (a : ℝ) (Y : Support n) (i : ι) : 0 ≤ kernel X B w a γ δ Y i :=
    div_nonneg (overlap_nonneg X B w hw _ Y i) (mul_nonneg (stretch_pos B hg hd).le (fanPrice_pos B _ _).le)

private lemma buy {α : Type*} [Fintype α] [DecidableEq α] {δ γ : ℝ} (hd : 0 < δ) (hg : 0 < γ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (Y : Support n) (p : α → Option α) (z : α → ι) (a : ℝ) :
    let G := installed X Y z
    let O (i : α) := overlapWeight X B w a (G (p i)) (z i)
    let K (i : α) := kernel X B w a γ δ (G (p i)) (z i)
    (∏ i, O i) ≤ currency B δ Y * (stretch B γ δ)^Fintype.card α * fanout p * ∏ i, K i := by
  intro G O K
  let t := stretch B γ δ
  have ht : 0 < t := stretch_pos B hg hd
  let u i := currency B δ (X (z i))
  have hx i : 0 < u i := Real.exp_pos _
  have hh i : 0 ≤ K i := kernel_pos X B hw hg hd a _ _
  have eq (i : α) : O i * u i = t * fanPrice B δ (G (p i)) * K i := by
    unfold O K kernel overlapWeight
    split
    next h =>
      have he : currency B (a+δ) (X (z i)) = currency B a (X (z i)) * u i := by
        rw [currency,add_mul,Real.exp_add]; rfl
      change _ = t * _ * (_ * _ / (t*_))
      rw [he]; have hb := fanPrice_pos B (G (p i)) δ; field_simp
    next h => simp
  apply le_of_mul_le_mul_right (a:=∏ i, u i) ?_ (Finset.prod_pos (fun i _ => hx i))
  calc
    _ = ∏ i, t * fanPrice B δ (G (p i)) * K i := by
      rw [← prod_mul_distrib]; exact prod_congr rfl fun i _ => eq i
    _ = (t^Fintype.card α * ∏ i, K i) * ∏ i, fanPrice B δ (G (p i)) := by
      simp_rw [prod_mul_distrib,Finset.prod_const,card_univ]; ring
    _ ≤ (t^Fintype.card α * ∏ i, K i) * ((fanout p:ℝ) * (currency B δ Y * ∏ i, u i)) :=
      mul_le_mul_of_nonneg_left (prod_fanPrice X B hd Y p z) (mul_nonneg (pow_nonneg ht.le _)
        (prod_nonneg fun i _ => hh i))
    _ = _ := by unfold t; ring

/-- Uniform at each finite D. This step pays all child factorials. -/
theorem trees_afford (m : ℕ) (D : Finset ι) (Y : Support n) {γ δ a : ℝ} (hg : 0 < γ)
    (hd : 0 < δ) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hh : Ac.Hit X B w (a+δ) γ) :
    ∑ p : Fin m → Option (Fin m), ∑ z : Fin m → D, forestWeight X B w a Y p (fun i => (z i).val) ≤
      currency B δ Y * (degreePrice B γ δ)^m := by
  let A := Fin m → Option (Fin m)
  let g p (z : Fin m → D) := forestWeight X B w a Y p (fun i => (z i).val)
  let t := stretch B γ δ
  let v := currency B δ Y
  let K := fun (Y : Support n) (i : D) => kernel X B w a γ δ Y i.val
  let Z := fun i : D => X i.val
  have hi Y i : 0 ≤ K Y i := kernel_pos X B hw hg hd a _ _
  have hk Y : ∑ i:D, K Y i ≤ 1 := by
    rw [← sum_subtype D (p:=(· ∈ D)) (fun _ => Iff.rfl)
      (kernel X B w a γ δ Y)]; exact kernel_sum X B hg hd hh Y D
  have hv : 0 ≤ v := (Real.exp_pos _).le
  have ht : 0 < t := stretch_pos B hg hd
  have hm : 0 < (m.factorial:ℝ) := by positivity
  have he (p : A) : (∑ z, g p z) ≤ v * t^m * fanout p / m.factorial := by
    rw [le_div_iff₀ hm,sum_mul]; by_cases H : Ranked p
    · let q (z : Fin m → D) := ∏ i, K (installed Z Y z (p i)) (z i)
      calc
        _ ≤ ∑ z : Fin m → D, (v * t^m * fanout p) * q z := sum_le_sum fun z _ => by
          unfold g; rw [overlap_eq X B w a Y p _ H,Fintype.card_fin,div_mul_cancel₀ _ hm.ne']
          simpa! only [Fintype.card_fin,q,v,t,K,Z,installed,Function.comp_def] using buy X B hd hg hw Y p (fun i => (z i).val) a
        _ ≤ _ := by
          rw [← mul_sum]; apply mul_le_of_le_one_right (by positivity)
          exact substochastic Y Z K p H hi hk
    have hz z : g p z = 0 := by simp [g,forestWeight,Sprouts,H]
    simp_rw [hz,zero_mul,sum_const_zero]; positivity
  change ∑ p:A, ∑ z, g p z ≤ _
  calc
    _ ≤ ∑ p:A, v * t^m * fanout p / m.factorial := sum_le_sum fun p _ => he p
    _ = v*t^m*(∑ p:A, (fanout p:ℝ)) / m.factorial := by rw [mul_sum,sum_div]
    _ ≤ v*t^m*((4:ℝ)^m*m.factorial) / m.factorial := by
      gcongr
      exact_mod_cast parent_fanout m
    _ = _ := by unfold degreePrice; change _ = v*(4*t)^m; rw [mul_pow]; field_simp
end YM.Push.AbsoluteSums.Trees
