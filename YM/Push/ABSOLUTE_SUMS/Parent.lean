import YM.Ac.Table
import YM.RG.Activities

/-!
# Numbered trees/forests, exponential combinatorial payment

These forests are combinatorial (not the choice of a tree gauge).
Attach the roots of all trees to an extra vertex. With `α` indexing
all but this vertex `none`, represent uniquely by a parent assignment
`p : α → Option α`, with ranks strictly decreasing within `α`.
Includes every possible branching multiplicity. May equally let `none`
carry an internal vertex for a **rooted** count. Child slots are NOT
implicitly ordered. The overlap conditions in the next module restrict
this count.

Two payments: products of nonnegative substochastic rows sum to at
most one on each such tree. For summing trees, we will lose one
factorial for each fiber size (= number of children). The second lemma
pays all those factorials at once: even summing over ALL parent maps,
one global factorial and an exponential is enough. This approach trades
a little in the final smallness constant for simpler occurrence
estimates and a direct geometric tail.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Trees
open Finset
open scoped BigOperators Classical

variable {α β : Type*}

def Ranked (p : α → Option α) : Prop := ∃ h : α → ℕ,
    ∀ i j, p i = some j → h j < h i

def label {τ : Type*} (Y : τ) (f : α → τ) : Option α → τ :=
    fun i => i.elim Y f




/-- Sum over all label assignments, retaining each whole label at every
parent and child. No condition on number of children. -/
lemma substochastic [Fintype α] [DecidableEq α] [Fintype β] {τ : Type*}
    (Y : τ) (X : β → τ) (K : τ → β → ℝ)
    (p : α → Option α) (h : Ranked p)
    (hk : ∀ i j, 0 ≤ K i j) (hr : ∀ i, ∑ j : β, K i j ≤ 1) :
    ∑ z : α → β, ∏ i, K (label Y (fun j => X (z j)) (p i)) (z i) ≤ 1 := by
  by_cases hα : Nonempty α
  swap
  · haveI : IsEmpty α := not_nonempty_iff.mp hα
    simp
  by_cases hβ : Nonempty β
  swap
  · haveI : IsEmpty β := not_nonempty_iff.mp hβ
    haveI : Nonempty α := hα
    simp
  obtain ⟨b⟩ := hβ
  obtain ⟨R,hR⟩ := h
  let value (z : α → β) (i : α) := label Y (fun j => X (z j)) (p i)
  let P := fun j : β => if j=b then (1:ℝ) else 0
  let w (s : Finset α) (z : α → β) (i : α) := if i∈s then K (value z i) (z i) else P (z i)
  let f (s : Finset α) (z : α → β) := ∏ i, w s z i
  have hp : ∑ j : β, P j = 1 := by simp [P]
  have hw s z i : 0 ≤ w s z i := by
    unfold w P; split
    · exact hk ..
    · split <;> norm_num
  have H (s : Finset α) : ∑ z, f s z ≤ 1 := by
    induction s using Finset.strongInduction with
    | H s IH =>
      rcases s.eq_empty_or_nonempty with he|he
      · subst s; simp only [f,w,notMem_empty,↓reduceIte]
        rw [← Fintype.prod_sum (fun (_:α) (i:β) => P i)]; simp only [hp,prod_const_one,le_refl]
      obtain ⟨i,hi,hm⟩ := Finset.exists_max_image s R he
      let t := s.erase i
      apply le_trans _ (IH t (erase_ssubset hi))
      let e := Equiv.funSplitAt i β
      have h (s : Finset α) : ∑ z, f s z = ∑ y : {j // j ≠ i} → β, ∑ a : β, f s (e.symm (a,y)) := by
        rw [Fintype.sum_equiv e (f s) (fun x => f s (e.symm x)) (fun x => by rw [e.symm_apply_apply]),
          Fintype.sum_prod_type,Finset.sum_comm]
      rw [h,h]; apply Finset.sum_le_sum; intro y _
      let z (a : β) := e.symm (a,y)
      let u (j : α) := w s (z b) j
      have at_i (a : β) : z a i = a := by
        have he := congr_arg Prod.fst (e.apply_symm_apply (a,y))
        exact he
      have eq (a b : β) (j : α) (hh : j ≠ i) : z a j = z b j := by
        have he (a) := congr_fun (congr_arg Prod.snd (e.apply_symm_apply (a,y))) ⟨j,hh⟩
        exact (he a).trans (he b).symm
      have mem (a : β) (j : α) (hj : j ∈ s) : value (z a) j = value (z b) j := by
        unfold value
        cases he : p j with
        | none => rfl
        | some k =>
          change X (z a k) = X (z b k)
          have hx : k ≠ i := fun eq => by
            subst k; exact lt_irrefl (R i) ((hR _ _ he).trans_le (hm _ hj))
          rw [eq a b _ hx]
      have hs (a : β) (j : α) (hj : j ≠ i) : w s (z a) j = u j := by
        unfold u w
        rw [eq a b _ hj]
        split
        next h => rw [mem a j h]
        next => rfl
      have ht (a : β) (j : α) (hj : j ≠ i) : w t (z a) j = u j := by
        rw [← hs a j hj]
        by_cases he : j∈s <;> simp [w,t,hj,he]
      let M := ∏ j∈univ.erase i, u j
      have hM : 0 ≤ M := Finset.prod_nonneg fun j _ => hw _ _ _
      have sk (a : β) : f s (z a) = K (value (z b) i) a * M := by
        unfold f M
        rw [← mul_prod_erase univ _ (mem_univ i)]
        congr 1
        · unfold w; rw [if_pos hi,mem a i hi,at_i a]
        apply prod_congr rfl; intro j hj; exact hs a j (mem_erase.mp hj).1
      have tk (a : β) : f t (z a) = P a * M := by
        unfold f M
        rw [← mul_prod_erase univ _ (mem_univ i)]
        congr 1
        · unfold w; rw [if_neg (notMem_erase i s),at_i a]
        apply prod_congr rfl; intro j hj; exact ht a j (mem_erase.mp hj).1
      change ∑ a : β, f s (z a) ≤ ∑ a, f t (z a)
      simp_rw [sk,tk,← sum_mul,hp]
      exact mul_le_mul_of_nonneg_right (hr (value (z b) i)) hM
  simpa only [f,w,value,mem_univ,↓reduceIte] using H univ

section Factorial

variable [DecidableEq β]

def children [Fintype α] (p : α → β) (i : β) : ℕ := (univ.filter (p · = i)).card

def fanout [Fintype α] [Fintype β] (p : α → β) : ℕ :=
  ∏ i : β, Nat.factorial (children p i)

lemma count_children [Fintype α] [Fintype β] (p : α → β) :
    ∑ i : β, children p i = Fintype.card α := by
  simpa only [Finset.sum_const, smul_eq_mul,mul_one,children,card_univ] using
    Finset.sum_fiberwise univ p (fun _ => (1:ℕ))

private lemma cons_card {n : ℕ} (p : Fin n → β) (i j : β) :
    children (Fin.cons i p) j = (if i=j then 1 else 0) + children p j := by
  have e {m : ℕ} (p : Fin m → β) : children p j = ∑ x : Fin m, if p x = j then 1 else 0 := by
    unfold children; simp
  rw [e (Fin.cons i p),e p,Fin.sum_univ_succ]; simp

lemma cons_fanout [Fintype β] {n : ℕ} (p : Fin n → β) (i : β) :
    fanout (Fin.cons i p) = (children p i + 1)*fanout p := by
  unfold fanout
  rw [← mul_prod_erase univ _ (mem_univ i),← mul_prod_erase univ _ (mem_univ i),← Nat.mul_assoc]
  congr 1
  · rw [cons_card p i i,if_pos rfl,add_comm,Nat.factorial_succ]
  apply prod_congr rfl; intro j hj
  rw [cons_card p i j, if_neg (Ne.symm (mem_erase.mp hj).1),zero_add]

variable (β) [Fintype β]

lemma cost_succ (n : ℕ) :
    ∑ p : Fin (n+1) → β, fanout p = (n + Fintype.card β) * ∑ p : Fin n → β, fanout p := by
  let e := Fin.consEquiv (fun _ : Fin (n+1) => β)
  rw [Fintype.sum_equiv e.symm _ (fun u => fanout (e u)) (fun x => by rw [e.apply_symm_apply]),
    Fintype.sum_prod_type,Finset.sum_comm,mul_sum]; apply Finset.sum_congr rfl; intro p _
  change ∑ i : β, fanout (Fin.cons i p) = _
  simp_rw [cons_fanout,← sum_mul,sum_add_distrib,count_children]
  simp

lemma total_fanout (n k : ℕ) (h : Fintype.card β=k+1) :
    ∑ p : Fin n → β, fanout p = (Nat.choose (n+k) k)*Nat.factorial n := by
  have H (m : ℕ) : Nat.choose (m+k) k * Nat.factorial m * Nat.factorial k =
      Nat.factorial (m+k) := by
    have he := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k m)
    rwa [Nat.add_sub_cancel, mul_right_comm] at he
  induction n with
  | zero =>
    have he (p : Fin 0 → β) (i : β) : children p i = 0 := by simp [children]
    simp only [fanout,he,Nat.factorial_zero,Finset.prod_const_one,Finset.sum_const,
      Finset.card_univ,zero_add,Nat.choose_self,Nat.mul_one]
    simp
  | succ m IH =>
    rw [cost_succ,IH,h]; apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k)
    rw [Nat.mul_assoc, H m, H (m+1), show m+1+k=m+k+1 by ring, Nat.factorial_succ, add_assoc]

lemma fanout_bound (n : ℕ) (h : Fintype.card β=n+1) :
    ∑ p : Fin n → β, fanout p ≤ 4^n * n.factorial := by
  rw [total_fanout β n n h]; apply Nat.mul_le_mul_right
  calc
    _ ≤ 2^(n+n) := Nat.choose_le_two_pow _ n
    _ = 4^n := by rw [pow_add,← mul_pow]; rfl

lemma parent_fanout (n : ℕ) :
    ∑ p : Fin n → Option (Fin n), fanout p ≤ 4^n * n.factorial :=
  fanout_bound _ n (by simp)

end Factorial
end YM.Push.AbsoluteSums.Trees
