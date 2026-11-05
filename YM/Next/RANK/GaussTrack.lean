import YM.Next.RANK.Gaussian

/-!
# Gaussian recursion on arbitrary monomial, match graph

No arity hypothesis. Even in degenerate symmetry budgets. For zero mean
and axes charged only across different marks, no self-pairs survive. Reconcile
with separate contour definition of Wick matching in the next file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Normal
open Function MvPolynomial Finset
open scoped BigOperators Classical

variable {A B : Type*} [DecidableEq A] {S : Type*} [LinearOrder S] (loc : A → S) {V : Type*}

-- free generators in arbitrary order
abbrev glyphs (Z : A → V) (p : Finset A) : poly V := ∏ j∈p, X (Z j)

lemma renew (m : V → ℂ) (Z : A → V) (p : Finset A) : slit m (glyphs Z p) =
    ∑ i∈p,(m (Z i)) • glyphs Z (p.erase i) := by
  induction p using Finset.induction_on with
  | empty => simp only [glyphs,prod_empty,sum_empty]; exact Derivation.map_one_eq_zero ..
  | @insert j p h ih =>
    rw [sum_insert h]; unfold glyphs at *; rw [prod_insert h,slit_prod,ih,mul_sum,C_mul',add_comm,erase_insert h]
    congr 1; refine Finset.sum_congr rfl fun i hi => ?_
    have he : i≠j := ne_of_mem_of_not_mem hi h
    rw [erase_insert_of_ne he.symm,prod_insert (notMem_mono (erase_subset ..) h),← mul_smul_comm]

lemma spring (m : V → ℂ) (Q : Symmetric V) (Z : A → V) (p : Finset A) {i : A} (hi : i ∉ p) :
    blend Q m (glyphs Z (insert i p)) = m (Z i)*blend Q m (glyphs Z p)+
      ∑ j∈p,Q.cov (Z i) (Z j)*blend Q m (glyphs Z (p.erase j)) := by
  rw [glyphs,prod_insert hi]; change blend Q m (X _ * glyphs _ _)=_
  rw [blended,renew,map_sum]; simp only [map_smul, smul_eq_mul]

-- matching representation for subsets
variable [Fintype A]
def Trace (p : Finset A) (P : Equiv.Perm A) := (P*P=1) ∧ (∀ i∈p, loc (P i) ≠ loc i) ∧ ∀ i,i∉p → P i=i
abbrev register (p : Finset A) := (Finset.univ: Finset (Equiv.Perm A)).filter (Trace loc p)

omit [DecidableEq A] [LinearOrder S] [Fintype A] in
lemma calls {p : Finset A} {P : Equiv.Perm A} (h : Trace loc p P) (i : A) : P (P i)=i := DFunLike.congr_fun h.1 i
omit [LinearOrder S] [Fintype A] in
lemma contains {p : Finset A} {P : Equiv.Perm A} (h : Trace loc p P) {i} (hp : i∈p) : P i ∈ p := by
  by_contra ht; have hx := h.2.2 _ ht; exact h.2.1 _ hp (congr_arg loc (P.injective hx))

def link (q : Symmetric V) (Z : A → V) (p : Finset A) (P : Equiv.Perm A) : ℂ :=
  ∏ i∈p.filter (fun i => loc i<loc (P i)),q.cov (Z i) (Z (P i))

def ringlet {i : A} (j : A) (P : Equiv.Perm A) := (Equiv.swap i j)*P

omit [LinearOrder S] [Fintype A] in
lemma connect {j : A} {p : Finset A} {a : A} (ha : a∈p) (hf : loc a ≠ loc j) (hb : j∉p) {P : Equiv.Perm A} (h : Trace loc (p.erase a) P) :
    Trace loc (insert j p) (ringlet (i:=j) a P) := by
  have hP : P a=a := h.2.2 _ (notMem_erase _ _); have hJ : P j=j := h.2.2 _ (notMem_mono (erase_subset ..) hb)
  let R := ringlet (i:=j) a P
  have hi : R a=j := by change Equiv.swap j a (P a)=_; rw [hP,Equiv.swap_apply_right]
  have hj : R j=a := by change Equiv.swap j a (P j)=_; rw [hJ,Equiv.swap_apply_left]
  have ht {k : A} (hx : k ≠ j) (hp : k ≠ a) : R k=P k := Equiv.swap_apply_of_ne_of_ne (mt (fun h => P.injective (h.trans hJ.symm)) hx) (mt (fun h => P.injective (h.trans hP.symm)) hp)
  constructor
  · ext k
    change R (R k)=k; rcases eq_or_ne k a with hg|hg <;> [rw [hg,hi,hj]; skip]; rcases eq_or_ne k j with h'|h'
    · rw [h',hj,hi]
    rw [ht h' hg, ht, calls loc h]
    · exact fun H => h' (P.injective (H.trans hJ.symm))
    exact fun H => hg (P.injective (H.trans hP.symm))
  constructor
  · intro i hs; change loc (R i)≠_
    rcases Finset.mem_insert.mp hs with g|g
    · rw [g,hj]; exact hf
    rcases eq_or_ne i a with u|u
    · rw [u,hi]; exact hf.symm
    rw [ht (ne_of_mem_of_not_mem g hb) u]; exact h.2.1 _ (mem_erase.mpr ⟨u,g⟩)
  intro i he; have hy : i≠j ∧ i∉p := by simpa only [Finset.mem_insert,not_or] using he
  rw [show ringlet a P=R from rfl,ht hy.1 (ne_of_mem_of_not_mem ha hy.2).symm]; exact h.2.2 _ (notMem_mono (erase_subset ..) hy.2)


omit [LinearOrder S] [Fintype A] in
lemma restored {j : A} {p : Finset A} (hb : j∉p) {P : Equiv.Perm A} (he : Trace loc (insert j p) P) :
    ∃ i ∈ p, ∃ Q, Trace loc (p.erase i) Q ∧ loc i≠loc j ∧ P=ringlet (i:=j) i Q := by
  let i := P j
  have hi : loc i ≠ loc j := he.2.1 _ (mem_insert_self ..)
  have hh : i ≠ j := fun H => hi (congr_arg loc H)
  have hp : P i=j := calls loc he _
  have hc : i ∈ p := (mem_insert.mp (contains loc he (mem_insert_self ..))).resolve_left hh
  let Q := ringlet (i:=j) i P
  have hj : Q j=j := Equiv.swap_apply_right j i; have hb' : Q i=i := by change Equiv.swap j i (P i)=_; rw [hp]; exact Equiv.swap_apply_left ..
  have he' {a : A} (hx : a ≠ j) (hv : a ≠ i) : Q a=P a :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hv (P.injective (h.trans hp.symm))) (fun h => hx (P.injective h))
  refine ⟨i,hc,Q,?_,hi,?_⟩
  · constructor
    · ext a; change Q (Q a)=_
      by_cases hv : a=i; · rw [hv,hb',hb']; rfl
      by_cases hx : a=j; · rw [hx,hj,hj]; rfl
      rw [he' hx hv, he', calls loc he]
      · rfl
      · exact fun H => hv (P.injective (H.trans hp.symm))
      exact fun H => hx (P.injective H)
    refine ⟨fun a h => ?_,fun a hv => ?_⟩
    · obtain ⟨h₁,h₂⟩ := mem_erase.mp h; rw [he' (ne_of_mem_of_not_mem h₂ hb) h₁]; exact he.2.1 _ (mem_insert_of_mem h₂)
    by_cases hh : a=i; · rw [hh,hb']
    by_cases ht : a=j; · rw [ht,hj]
    rw [he' ht hh]; exact he.2.2 _ (show a∉insert j p from fun he => (mem_insert.mp he).elim ht (fun H => hv (mem_erase.mpr ⟨hh,H⟩)))
  rw [show ringlet (i:=j) i Q=(Equiv.swap j i*(Equiv.swap j i*P)) from rfl, ← mul_assoc]; simp

omit [Fintype A] in
lemma tracks (q : Symmetric V) (Z : A → V) {P : Equiv.Perm A} {a j : A} {p : Finset A} (hp : a∈p) (hj : j∉p) (hx : loc a≠loc j)
    (he : Trace loc (p.erase a) P) :
    link loc q Z (insert j p) (ringlet (i:=j) a P) = q.cov (Z j) (Z a)*link loc q Z (p.erase a) P := by
  let R := ringlet (i:=j) a P
  have h' := connect loc hp hx hj he
  have hz : P j=j := he.2.2 _ (notMem_mono (erase_subset ..) hj)
  have hh : R j=a := by change Equiv.swap j a (P j)=_; rw [hz,Equiv.swap_apply_left]
  have hi : R a=j := by rw [← hh]; exact calls loc h' _
  let F := fun i => if loc i<loc (P i) then q.cov (Z i) (Z (P i)) else 1
  let E := fun i => if loc i<loc (R i) then q.cov (Z i) (Z (R i)) else 1
  have hX (p : Finset A) (P : Equiv.Perm A) : link loc q Z p P=∏ i∈p,(if loc i<loc (P i) then q.cov (Z i) (Z (P i)) else 1) := prod_filter ..
  rw [hX,hX]
  change (∏ i∈insert j p,E i)=_*∏ i∈p.erase a,F i
  have ht : (∏ i∈p.erase a,E i)=∏ i∈p.erase a,F i := by
    refine prod_congr rfl fun i ha => ?_; obtain ⟨h₁,h₂⟩ := mem_erase.mp ha
    have hu := ne_of_mem_of_not_mem h₂ hj
    have hw : R i=P i := Equiv.swap_apply_of_ne_of_ne (fun h => hu (P.injective (h.trans hz.symm))) (fun h => h₁ (P.injective (h.trans (he.2.2 _ (notMem_erase a p)).symm)))
    simp only [E,F,hw]
  have hw : E j*E a=q.cov (Z j) (Z a) := by
    rcases lt_or_gt_of_ne hx with H|H <;> simp only [E,hh,hi,H,H.not_gt,↓reduceIte,one_mul,mul_one]
    exact q.symm ..
  rw [prod_insert hj, ← Finset.mul_prod_erase _ E hp,← mul_assoc, hw, ht]

lemma headed (q : Symmetric V) (Z : A → V) (H : ∀ a b, loc a=loc b → q.cov (Z a) (Z b)=0) (p : Finset A) :
    blend q 0 (glyphs Z p)=∑ P ∈ register loc p, link loc q Z p P := by
  classical
  induction p using Finset.strongInduction with
  | H p IH =>
  by_cases ht : p=∅
  · subst p; have he : register loc ∅={1} := by
      ext i; rw [register, mem_filter,mem_singleton]; simp only [mem_univ,true_and]; constructor
      · intro h; ext1 a; exact h.2.2 a (notMem_empty _)
      rintro rfl; exact ⟨one_mul _,fun i => False.elim ∘ notMem_empty i,fun _ _ => rfl⟩
    rw [glyphs,prod_empty,fresh,he,sum_singleton]; exact prod_empty.symm
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr ht
  let D := p.erase i
  have hz : i ∉ D := notMem_erase i p
  have he : p=insert i D := (insert_erase hi).symm
  have hh : D ⊂ p := Finset.erase_ssubset hi
  rw [he,spring ..]; rotate_left; exact hz
  simp only [Pi.zero_apply, zero_mul,zero_add]
  have hu a : blend q 0 (glyphs Z (D.erase a)) = ∑ P ∈ register loc (D.erase a), link loc q Z (D.erase a) P := IH _ (Finset.ssubset_of_subset_of_ssubset (erase_subset ..) hh)
  simp_rw [hu,Finset.mul_sum]
  let W (a : A) := (register loc (D.erase a)).filter (fun _ => loc a≠loc i)
  have hr a : ∑ P ∈ register loc (D.erase a), q.cov (Z i) (Z a)*link loc q Z (D.erase a) P=∑ P∈ W a, q.cov (Z i) (Z a)*link loc q Z (D.erase a) P := by
    symm; apply sum_subset (filter_subset ..); intro P hp hj
    rw [H i a (by by_contra ht; exact hj (mem_filter.mpr ⟨hp,Ne.symm ht⟩)), zero_mul]
  simp_rw [hr]
  rw [Finset.sum_sigma' D W (fun a P => q.cov (Z i) (Z a)*link loc q Z (D.erase a) P)]
  let f (b : (x : A) × Equiv.Perm A) := ringlet (i:=i) b.1 b.2
  apply sum_bij (fun a _ => f a)
  · rintro ⟨a,P⟩ hp
    obtain ⟨h₁,h₂⟩ := mem_sigma.mp hp; obtain ⟨u,h₂⟩ := mem_filter.mp h₂; exact mem_filter.mpr ⟨mem_univ _, connect loc h₁ h₂ hz (mem_filter.mp u).2⟩
  · have ht (a : A) (P : Equiv.Perm A) (hp : P∈W a) : (f ⟨a,P⟩) i=a := by
      have hx : Trace loc (D.erase a) P := (mem_filter.mp (mem_filter.mp hp).1).2
      change Equiv.swap i a (P i) = _; rw [hx.2.2 _ (notMem_mono (erase_subset ..) hz),Equiv.swap_apply_left]
    rintro ⟨a,P⟩ h₁ ⟨j,Q⟩ h₂ hx
    have he := DFunLike.congr_fun hx i
    rw [ht _ _ (mem_sigma.mp h₁).2,ht _ _ (mem_sigma.mp h₂).2] at he; change a=j at he; subst j
    have hx' : P=Q := mul_left_cancel (show Equiv.swap i a * P = Equiv.swap i a * Q from hx); rw [hx']
  · intro P hp
    obtain ⟨a,h₁,Q,h₂,h₃,G⟩ := restored loc hz (mem_filter.mp hp).2
    refine ⟨⟨a,Q⟩, mem_sigma.mpr ⟨h₁,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,h₂⟩,h₃⟩⟩,G.symm⟩
  rintro ⟨a,P⟩ hp
  obtain ⟨ha,hb⟩ := mem_sigma.mp hp; obtain ⟨hp,hf⟩ := mem_filter.mp hb
  exact (tracks loc q Z ha hz hf (mem_filter.mp hp).2).symm
end YM.Next.Rank.Normal
