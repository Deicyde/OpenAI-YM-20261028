import YM.Marker.Truncated
import YM.Next.MULTISOURCE.Split

/-! Finite augmentation ideal identities (no degree loss/cutoff truncation of surviving monomials). -/

set_option autoImplicit false
noncomputable section

namespace YM.Multi

open Marker Finset
open scoped BigOperators

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {R : Census V} {S : Census W}

def dilationL (R : Census V) (a : V → ℂ) : Poly R →ₗ[ℂ] Poly R where
  toFun p := Poly.inject fun i => (∏ v∈i.val,a v) * p.part i
  map_add' p q := by
    ext i
    change (∏ v ∈ i.val, a v)*(p.part i+q.part i) = _*p.part i + _*q.part i
    rw [mul_add]
  map_smul' c p := by
    ext i
    change (∏ v ∈ i.val, a v)*(c * p.part i) = c * ((∏ v ∈ i.val, a v)*p.part i)
    ring

lemma dilationL_send (p : R.Mode) (t : ℂ) (a : V → ℂ) :
    dilationL R a (Poly.send p t) = Poly.send p ((∏ v ∈ p.val, a v)*t) := by
  ext q
  change (∏ v∈q.val,a v) * _ = _
  by_cases e : q=p
  · subst q; simp
  simp [e]

def dilation (R : Census V) (a : V → ℂ) : Poly R →ₐ[ℂ] Poly R := by
  refine AlgHom.ofLinearMap (dilationL R a) ?_ ?_
  · change dilationL R a (Poly.send R.quiet 1)=_
    rw [dilationL_send]
    change Poly.send R.quiet ((∏ v∈∅, a v)*_) = _
    rw [prod_empty, one_mul]; rfl
  have hp (i j : R.Mode) (r t : ℂ) : dilationL R a (Poly.send i r * Poly.send j t) =
      dilationL R a (Poly.send i r) * dilationL R a (Poly.send j t) := by
    rw [dilationL_send, dilationL_send]
    by_cases h : ∃ z, Poly.merges i j z
    · obtain ⟨z,h⟩ := h
      rw [send_prod h,dilationL_send,send_prod h]
      congr 1; rw [← h.2, prod_union h.1]; ring
    rw [send_noProd h, send_noProd h, map_zero]
  intro x y
  rw [← Poly.studs x, ← Poly.studs y]
  simp_rw [Finset.sum_mul, Finset.mul_sum, map_sum, hp, Finset.sum_mul, Finset.mul_sum]

lemma dilation_send (p : R.Mode) (t : ℂ) (a : V → ℂ) :
    dilation R a (Poly.send p t) = Poly.send p ((∏ v ∈ p.val, a v)*t) := dilationL_send ..

lemma dilation_part (p : Poly R) (a : V → ℂ) (x : R.Mode) :
    (dilation R a p).part x = (∏ v∈x.val,a v) * p.part x := rfl

@[simp] lemma part_quiet_hot (x : Hot R) (a : ℂ) : (Poly.send x.val a).part R.quiet=0 := by
  rw [Poly.part_send, if_neg (show R.quiet≠x.val from fun h => Finset.nonempty_iff_ne_empty.mp
    x.property (congrArg Subtype.val h.symm))]

section
variable [Fintype V] [Fintype W]

lemma pass_extended (a : Poly R) (ha : a.part R.quiet=0) {N : ℕ} (hN : Fintype.card V ≤ N) :
    Poly.pass a = ∑ i ∈ Finset.range (N+1), (i.factorial:ℂ)⁻¹ • a^i := by
  apply Finset.sum_subset (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) (by omega)))
  intro i _ hi
  rw [Poly.stops a ha _ ?_, smul_zero]
  simpa [Finset.mem_range] using hi

lemma pass_map (f : Poly R →ₐ[ℂ] Poly S) (a : Poly R) (ha : a.part R.quiet = 0)
    (hf : (f a).part S.quiet = 0) : f (Poly.pass a) = Poly.pass (f a) := by
  let x := Fintype.card V
  let y := Fintype.card W
  rw [pass_extended a ha (le_max_left x y), pass_extended _ hf (le_max_right x y)]
  simp

/- Multiplying arbitrary nilpotent exponentials can be done by binomial.
   We only need appending a squarezero occurrence; pay for one last term
   by nonempty keys even in the arity-one ring. -/
lemma final_vanish (x a : Poly R) (hx : x.part R.quiet=0) (ha : a.part R.quiet=0) :
    x^(Fintype.card V) * a = 0 := by
  ext b; rw [Poly.part_nil,Poly.part_mul]
  apply sum_eq_zero; intro i hi
  apply sum_eq_zero; intro j hj
  split <;> rename_i h
  · by_cases e : j = R.quiet
    · subst j; simp [ha]
    have he : j.val.Nonempty := nonempty_iff_ne_empty.mpr fun h' => e (Subtype.ext h')
    have hg : i.val.card < b.val.card := by
      rw [← h.2,card_union_of_disjoint h.1]; exact Nat.lt_add_of_pos_right (card_pos.mpr he)
    rw [Poly.high x hx _ i (lt_of_lt_of_le hg (Finset.card_le_univ _)),zero_mul]
  rfl

lemma append_pass (x a : Poly R) (hx : x.part R.quiet=0) (ha : a.part R.quiet=0) (he : a*a=0) :
    Poly.pass (x+a) = Poly.pass x * (1+a) := by
  have hk (n : ℕ) : (x+a)^(n+1)=x^(n+1)+(n+1:ℕ) • (x^n*a) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ (x+a) (n+1), ih, add_mul]
      simp only [mul_add, nsmul_eq_mul, mul_assoc, he, mul_zero, add_zero, Nat.cast_add_one,
        pow_succ]; ring
  have H (n : ℕ) : ((n+1).factorial:ℂ)⁻¹ • (x+a)^(n+1) =
      ((n+1).factorial:ℂ)⁻¹ • x^(n+1) + ((n.factorial:ℂ)⁻¹ • x^n)*a := by
    rw [hk, smul_add]
    congr 1
    rw [smul_mul_assoc, ← Nat.cast_smul_eq_nsmul ℂ, ← mul_smul]
    have hg : ((n+1).factorial:ℂ)⁻¹ * (↑(n+1:ℕ):ℂ) = (n.factorial:ℂ)⁻¹ := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), mul_one]
    rw [hg]
  unfold Poly.pass
  rw [mul_add, mul_one, sum_mul]
  rw [Finset.sum_range_succ' (fun i => (i.factorial:ℂ)⁻¹ • (x+a)^i), Finset.sum_range_succ', Finset.sum_range_succ _ (Fintype.card V)]
  simp_rw [H]
  rw [Finset.sum_add_distrib]
  rw [smul_mul_assoc, final_vanish x a hx ha]
  simp only [smul_zero, add_zero,pow_zero]; abel

lemma pass_sum_send {X : Type*} (s : Finset X) (f : X → Hot R) (f' : X → ℂ) :
    Poly.pass (∑ i∈s, Poly.send (f i).val (f' i))=∏ i∈s, (1+Poly.send (f i).val (f' i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [prod_empty, sum_empty, Poly.pass,sum_eq_single 0]
    · simp
    · intro b _ hb; simp [hb]
    simp
  | insert i s h ih =>
    rw [sum_insert h,prod_insert h,add_comm,append_pass,ih,mul_comm]
    · rw [Poly.part_sum]; exact sum_eq_zero fun j _ => part_quiet_hot (f j) _
    · apply part_quiet_hot
    · refine send_noProd ?_ _ _
      rintro ⟨z,hz⟩
      obtain ⟨v,hv⟩ := (f i).property
      exact Finset.disjoint_left.mp hz.1 hv hv
end

end YM.Multi
