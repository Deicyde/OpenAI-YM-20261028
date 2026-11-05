import Mathlib.RingTheory.Nilpotent.Exp
import YM.Next.EXTRACTION.Tails


/-!
# Birth algebra

Per site square-zero alternatives. Mixed density `exp` already implemented
as finite factorial sum (`Poly.pass`, NOT ordinary complex exp of a
point); use its actual multiplicative law with positive-degree inputs. Also
actual coefficient support tests and majorants for gathering. Does not make
a no-zero-divisors assumption on `Poly`!
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Push.GridApprox.Nil
open Function MeasureTheory Set Marker
open scoped Topology BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}

private local instance : Module ℚ (Poly R) := Module.compHom _ (Rat.castHom ℂ)


private lemma exp_eq (a : Poly R) (ha : a.part R.quiet = 0) : IsNilpotent.exp a = Poly.pass a := by
  rw [IsNilpotent.exp_eq_sum (a.stops ha (Fintype.card V+1) (Nat.lt_succ_self _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (((Rat.castHom ℂ) ((i.factorial:ℚ)⁻¹)) • (a^i)) = _
  simp











@[simp] lemma pass_zero : Poly.pass (0:Poly R) = 1 := by rw [← exp_eq _ (by simp)]; exact IsNilpotent.exp_zero



/-- No use of wrong markers can be activated by multiplication. -/
def Scoped (A : Set V) (x : Poly R) := ∀ i, ¬ ((i.val:Set V) ⊆ A) → x.part i=0
lemma scope_send (A : Set V) (s : R.Mode) (c : ℂ) (h : (s.val:Set V) ⊆ A) : Scoped A (Poly.send s c) := by
  intro i hi; have he : i≠s := fun hx => hi (hx.symm ▸ h); simp [he]
lemma scope_plus {A : Set V} {f g : Poly R} (ha : Scoped A f) (hb : Scoped A g) : Scoped A (f+g) :=
  fun x hx => by rw [Poly.part_plus,ha x hx,hb x hx,add_zero]

lemma scope_mul {A : Set V} {f g : Poly R} (ha : Scoped A f) (hb : Scoped A g) : Scoped A (f*g) := by
  intro x hx
  rw [Poly.part_mul]; refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split
  next hi =>
    by_cases he : (i.val:Set V) ⊆ A
    · have hh : ¬ ((j.val:Set V) ⊆ A) := fun hC => hx (by rw [← hi.2,Finset.coe_union]; exact union_subset he hC)
      rw [hb j hh,mul_zero]
    rw [ha i he,zero_mul]
  rfl
lemma scope_prod {ι : Type*} {A : Set V} (s : Finset ι) (f : ι → Poly R) (h : ∀ i∈s, Scoped A (f i)) :
    Scoped A (∏ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]; exact scope_send A R.quiet 1 <| by simp [Census.quiet]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact scope_mul (h i (Finset.mem_insert_self ..)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Absolute majorant array; nonnegative in use, `real` ring argument not
needed. Retain per-mode values under *all* U before summing weights. -/
abbrev Sheet (R : Census V) := R.Mode → ℝ

def wordsPrice (w : V → ℝ) (a : Sheet R) := ∑ i, Poly.toll w i * a i

def combine (a b : Sheet R) : Sheet R := fun i => ∑ j,∑ k, if Poly.merges j k i then a j*b k else 0

lemma merged_nn (a b : Sheet R) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ combine a b := by
  intro i; unfold combine; refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  split; exacts [mul_nonneg (ha j) (hb k),le_refl _]

lemma merged_cap {a b : Poly R} (U W : Sheet R) (ha : ∀ i, ‖a.part i‖ ≤ U i)
    (hb : ∀ i, ‖b.part i‖ ≤ W i) (i : R.Mode) : ‖(a*b).part i‖ ≤ combine U W i := by
  unfold combine; rw [Poly.part_mul]; apply le_trans (norm_sum_le ..) (Finset.sum_le_sum ?_)
  intro j hj; apply le_trans (norm_sum_le ..) (Finset.sum_le_sum ?_); intro k hk
  split
  next he => rw [norm_mul]; exact mul_le_mul (ha j) (hb k) (norm_nonneg _) ((norm_nonneg _).trans (ha _))
  next he => simp

lemma merged_price (a b : Sheet R) (ha : 0 ≤ a) (hb : 0 ≤ b) (w : V → ℝ) (he : ∀ i,0<w i) :
    wordsPrice w (combine a b) ≤ wordsPrice w a*wordsPrice w b := by
  let f (p i j : R.Mode) := Poly.toll w p * (if Poly.merges i j p then a i*b j else 0)
  have ht : wordsPrice w (combine a b)=∑ i, ∑ j, ∑ p, f p i j := by
    unfold f wordsPrice combine; simp only [Finset.mul_sum]
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [ht]; unfold wordsPrice
  rw [Finset.sum_mul]; simp only [Finset.mul_sum]; refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hh : ∃ p, Poly.merges i j p
  · obtain ⟨p,hp⟩ := hh
    rw [Finset.sum_eq_single p (fun k _ hk => ?_) (by simp)]
    · unfold f; rw [if_pos hp,Poly.multiplier i j p hp]; exact le_of_eq (by ring)
    have h : ¬ Poly.merges i j k := fun hx => hk (Subtype.ext (hx.2.symm.trans hp.2))
    unfold f; rw [if_neg h,mul_zero]
  push Not at hh
  simp only [f, hh, ↓reduceIte,mul_zero,Finset.sum_const_zero]
  exact mul_nonneg (mul_nonneg (Poly.worth he i).le (ha _)) (mul_nonneg (Poly.worth he j).le (hb _))

/-- Existence avoids specifying a fold order. Uniform every U.
Useful also where many addresses pay the price once. -/
lemma all_prices {ι X : Type*} (s : Finset ι) (A : ι → Sheet R) (p : ι → ℝ) (f : X → ι → Poly R) (w : V → ℝ)
    (hw : ∀ i,0<w i) (ha : ∀ i, 0 ≤ A i) (hp : ∀ i, wordsPrice w (A i) ≤ p i)
    (he : ∀ x i v, ‖(f x i).part v‖ ≤ A i v) :
    ∃ q : Sheet R, 0 ≤ q ∧ wordsPrice w q ≤ ∏ i∈s,p i ∧
      ∀ x v, ‖(∏ i∈s, f x i).part v‖ ≤ q v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨(fun v => if v=R.quiet then 1 else 0),fun v => ?_, ?_,fun x v => ?_⟩
    · change 0 ≤ if v=R.quiet then 1 else (0:ℝ)
      split; exacts [zero_le_one,le_rfl]
    · simp [wordsPrice, mul_ite]
    rw [Finset.prod_empty,Poly.one_part]; by_cases h : v=R.quiet <;> simp [h]
  | insert i s hi ih =>
    obtain ⟨q,hq,hb,hs⟩ := ih
    have hn (a : Sheet R) (ha : 0≤a) : 0 ≤ wordsPrice w a := Finset.sum_nonneg fun i _ => mul_nonneg (Poly.worth hw _).le (ha _)
    refine ⟨combine (A i) q,merged_nn (A i) q (ha _) hq,?_,fun x v => ?_⟩
    · rw [Finset.prod_insert hi]; exact (merged_price _ _ (ha _) hq w hw).trans
        (mul_le_mul (hp _) hb (hn q hq) ((hn _ (ha i)).trans (hp i)))
    rw [Finset.prod_insert hi]; exact merged_cap _ _ (he x i) (hs x) v
end YM.Push.GridApprox.Nil
