import YM.Next.EXTRACTION.Tails

/-!
# Evaluating complete linear polynomial insertion in the actual nilpotent census

Coefficient k before ANY limits. No treating nilpotent truncation as an
ordinary exponential at a positive array. Application to initialization of
multi-source `Bands`, not a propagation rule/trajectory.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.LinearMarkers
open Function Finset Marker
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}

def linear (R : Census V) (f : V → ℂ) := ∑ i : V,Poly.send (R.fire i) (f i)

def monomial (R : Census V) (f : V → ℂ) (i : V) := Poly.send (R.fire i) (f i)
def factor (R : Census V) (f : V → ℂ) (i : V) := 1+monomial R f i

omit [Fintype V] in
theorem mono_add (f g : V → ℂ) (i : V) : monomial R (f+g) i = monomial R f i + monomial R g i := by
  ext v; simp only [monomial,Poly.part_plus,Poly.part_send,Pi.add_apply]; split <;> ring

omit [Fintype V] in
theorem combine (f g : V → ℂ) (i : V) : factor R f i * factor R g i = factor R (f+g) i := by
  suffices monomial R f i * monomial R g i=0 by unfold factor; rw [mono_add]; grind
  ext v
  have he : ¬ Poly.merges (R.fire i) (R.fire i) v := fun h =>
    Finset.disjoint_left.mp h.1 (mem_singleton_self _) (mem_singleton_self _)
  change (Poly.prod (Poly.send (R.fire i) (f i)) (Poly.send (R.fire i) (g i))).part _ = _
  rw [Poly.cart,if_neg he, Poly.part_nil]

def erase (R : Census V) (x : R.Mode) (i : V) : R.Mode := ⟨x.val.erase i, R.down x.property _ (Finset.erase_subset ..)⟩

omit [Fintype V] in
lemma merges_fire (y x : R.Mode) (i : V) : Poly.merges (R.fire i) y x ↔ i ∈ x.val ∧ y=erase R x i := by
  refine ⟨fun ⟨hd,he⟩ => ?_,?_⟩
  · have hy : i ∉ y.val := Finset.disjoint_left.mp hd (Finset.mem_singleton_self i)
    refine ⟨he ▸ Finset.mem_union_left _ (Finset.mem_singleton_self i), Subtype.ext (by
      change y.val = x.val.erase i; rw [← he,Census.fire]; ext j; simp; exact fun h he => hy (he ▸ h))⟩
  rintro ⟨h,rfl⟩; exact ⟨by simp [Census.fire,erase], by simp [Census.fire,erase,insert_erase h]⟩

omit [Fintype V] in
lemma extend (f : V → ℂ) (i : V) (a : Poly R) (x : R.Mode) : (monomial R f i * a).part x = if i∈x.val then
    f i * a.part (erase R x i) else 0 := by
  rw [Poly.part_mul, sum_eq_single (R.fire i)]
  · simp only [monomial,Poly.part_send,merges_fire]
    by_cases h : i∈x.val <;> simp [h]
  · intro j _ hj; simp [monomial, hj]
  simp

omit [Fintype V] in
lemma product_one (f : V → ℂ) (s : Finset V) (x : R.Mode) : (∏ i ∈ s,monomial R f i).part x = if s=x.val then ∏ i ∈ s,f i else 0 := by
  induction s using Finset.induction_on generalizing x with
  | empty => by_cases h : x=R.quiet <;> simp [h,Census.quiet,Subtype.ext_iff,eq_comm] at *
  | insert i s h ih =>
    rw [prod_insert h,prod_insert h,extend,ih]; unfold erase
    by_cases he : x.val = insert i s
    · simp [he,h]
    by_cases hx : i ∈ x.val
    · have hh : s ≠ x.val.erase i := fun hz => he (by rw [hz,insert_erase hx])
      simp [Ne.symm he,hx,hh]
    simp [hx,Ne.symm he]

theorem across (f : V → ℂ) (x : R.Mode) : (∏ i : V,factor R f i).part x = ∏ i∈x.val,f i := by
  unfold factor
  rw [Finset.prod_one_add, Poly.part_sum]; simp [product_one]

theorem linear_add (f g : V → ℂ) : linear R (f+g)=linear R f+linear R g := by
  unfold linear; rw [← Finset.sum_add_distrib]; exact sum_congr rfl fun i _ => mono_add f g i

theorem homogeneous (f : V → ℂ) (k : ℕ) (x : R.Mode) : ((linear R f)^k).part x = if x.val.card=k then
    (k.factorial:ℂ) * ∏ i∈x.val,f i else 0 := by
  induction k generalizing x with
  | zero => by_cases h : x.val=∅ <;> simp [Subtype.ext_iff,Census.quiet,h]
  | succ k ih =>
    rw [pow_succ']; nth_rw 1 [show linear R f = ∑ i,monomial R f i from rfl]; rw [Finset.sum_mul,Poly.part_sum]
    simp_rw [extend (a:= (linear R f)^k), ih]
    rw [Finset.sum_ite_mem,Finset.univ_inter]
    by_cases hx : x.val.card=k+1
    · rw [if_pos hx]
      have he (i : V) (hi : i∈x.val) : f i*(if (erase R x i).val.card=k then (k.factorial:ℂ)*∏ v∈(erase R x i).val, f v else 0) =
          k.factorial*∏ v∈x.val,f v := by
        rw [if_pos (by simp [erase,card_erase_of_mem hi,hx])]; unfold erase; dsimp only; rw [← mul_prod_erase _ _ hi]; ring
      rw [Finset.sum_congr rfl he,Finset.sum_const,hx,nsmul_eq_mul,Nat.factorial_succ, Nat.cast_mul,mul_assoc]
    rw [if_neg hx]; apply sum_eq_zero; intro i hi
    have he := card_erase_add_one hi
    rw [if_neg]; · exact mul_zero _
    change (x.val.erase i).card ≠ k; omega

theorem passing (f : V → ℂ) : Poly.pass (linear R f) = ∏ i : V, factor R f i := by
  ext x
  simp_rw [across,Poly.pass, Poly.part_sum,Poly.part_smul, homogeneous, mul_ite, mul_zero]
  have hx : x.val.card∈range (Fintype.card V+1) := mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _))
  rw [sum_ite_eq,if_pos hx,inv_mul_cancel_left₀ (by exact_mod_cast (Nat.factorial_ne_zero x.val.card) : (x.val.card.factorial:ℂ)≠0)]

end YM.WilsonStartup.LinearMarkers
