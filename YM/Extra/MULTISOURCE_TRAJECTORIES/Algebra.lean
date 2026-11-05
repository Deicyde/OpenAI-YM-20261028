import Mathlib.RingTheory.Nilpotent.Exp
import YM.Next.EXTRACTION.Base

/-!
# Exact coefficient algebra for joint trajectories

Exponential on the marked ideal of the *existing* commuting square-zero marker
algebra (including any of its allowed-set truncations); an inverse on 1 + that
ideal obtained by a triangular recursion by number of markers. No analytic
logarithm and no assumption of independence at any distance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Finset Marker Function
open scoped BigOperators ContDiff
variable {V : Type*} [DecidableEq V] {R : Census V}

lemma part_sub (a b : Poly R) (i : R.Mode) : (a-b).part i = a.part i-b.part i := rfl

lemma send_add (s : R.Mode) (a b : ℂ) : Poly.send s (a+b) = Poly.send s a + Poly.send s b := by
  ext i
  simp only [Poly.part_plus, Poly.part_send]; split <;> simp

lemma tagged_mul (x y z : R.Mode) (h : Poly.merges x y z) (a b : ℂ) :
    Poly.send x a * Poly.send y b = Poly.send z (a*b) := by
  ext i
  rw [Poly.part_send]; change (Poly.prod _ _).part i = _; rw [Poly.cart]
  have he : Poly.merges x y i ↔ i = z :=
    ⟨fun hh => Subtype.ext (hh.2.symm.trans h.2), fun e => e.symm ▸ h⟩
  simp only [he]

lemma merges_of_tagged_mul {x y : R.Mode} {a b : ℂ} (h : Poly.send x a * Poly.send y b ≠ 0) :
    ∃ z, Poly.merges x y z := by
  by_contra he
  push Not at he
  apply h; ext i
  change (Poly.prod _ _).part i = 0
  rw [Poly.cart, if_neg (he i)]

section Mates
variable {ι : Type*} (tag : ι → R.Mode)

def Fits (s : Finset ι) := (s : Set ι).PairwiseDisjoint (fun i => (tag i).val) ∧
  s.biUnion (fun i => (tag i).val) ∈ R.choices

lemma Fits.subset {s t : Finset ι} (h : Fits tag s) (ht : t ⊆ s) : Fits tag t := by
  refine ⟨h.1.subset (coe_subset.mpr ht), R.down h.2 _ (biUnion_subset.mpr fun i hi => ?_)⟩
  exact subset_biUnion_of_mem (fun i => (tag i).val) (ht hi)

def unionTag (s : Finset ι) (h : Fits tag s) : R.Mode := ⟨_,h.2⟩

lemma fits_empty : Fits tag ∅ := ⟨by simp, by simpa only [biUnion_empty] using R.blank⟩

lemma fits_singleton (i : ι) : Fits tag {i} := ⟨by simp,by simp⟩

lemma tagged_prod (s : Finset ι) (h : Fits tag s) (a : ι → ℂ) :
    ∏ i∈s,Poly.send (tag i) (a i) = Poly.send (unionTag tag s h) (∏ i∈s,a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty,prod_empty, show unionTag tag ∅ h = R.quiet from Subtype.ext biUnion_empty]
    rfl
  | insert i s hi ih =>
    have hs := h.subset tag (subset_insert i s)
    rw [prod_insert hi, prod_insert hi, ih hs]
    apply tagged_mul
    refine ⟨(disjoint_biUnion_right ..).mpr (fun j hj => ?_), biUnion_insert.symm⟩
    exact h.1 (mem_insert_self ..) (mem_insert_of_mem hj) (fun e => hi (e.symm ▸ hj))

lemma fits_of_tagged_prod {s : Finset ι} {a : ι → ℂ} (h : ∏ i∈s,Poly.send (tag i) (a i) ≠ 0) :
    Fits tag s := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fits_empty tag
  | insert i s hi ih =>
    rw [prod_insert hi] at h
    have hs := ih (right_ne_zero_of_mul h)
    rw [tagged_prod tag s hs] at h
    obtain ⟨z,hdis,hz⟩ := merges_of_tagged_mul h
    refine ⟨?_, by rw [biUnion_insert]; exact hz ▸ z.property⟩
    intro j hj k hk hjk; rw [mem_coe,mem_insert] at hj hk
    obtain rfl|ha := hj <;> obtain rfl|hb := hk
    · contradiction
    · exact (disjoint_biUnion_right ..).mp hdis k hb
    · exact ((disjoint_biUnion_right ..).mp hdis j ha).symm
    exact hs.1 ha hb hjk

lemma toll_union (s : Finset ι) (h : Fits tag s) (w : V → ℝ) :
    Poly.toll w (unionTag tag s h) = ∏ i∈s, Poly.toll w (tag i) := prod_biUnion h.1
end Mates

section Exp
variable [Fintype V]

private local instance : Module ℚ (Poly R) := Module.compHom _ (algebraMap ℚ ℂ)

private lemma exp_eq (x : Poly R) (h : x.part R.quiet=0) : IsNilpotent.exp x = Poly.pass x := by
  rw [IsNilpotent.exp_eq_sum (Poly.stops x h _ (Nat.lt_succ_self _))]
  apply sum_congr rfl
  intro i _
  change (algebraMap ℚ ℂ ((i.factorial:ℚ)⁻¹)) • (x^i) = _
  simp

lemma pass_add {x y : Poly R} (hx : x.part R.quiet=0) (hy : y.part R.quiet=0) :
    Poly.pass (x+y) = Poly.pass x * Poly.pass y := by
  rw [← exp_eq x hx,← exp_eq y hy,← exp_eq (x+y) (by simp [hx,hy])]
  exact IsNilpotent.exp_add_of_commute (Commute.all ..) ⟨_,Poly.stops x hx _ (Nat.lt_succ_self _)⟩
    ⟨_,Poly.stops y hy _ (Nat.lt_succ_self _)⟩

lemma pass_zero : Poly.pass (0 : Poly R) = 1 := by rw [← exp_eq 0 rfl, IsNilpotent.exp_zero]

lemma pass_send {i : R.Mode} (h : i.val.Nonempty) (c : ℂ) :
    Poly.pass (Poly.send i c) = 1 + Poly.send i c := by
  have ht : R.quiet ≠ i := fun e => h.ne_empty (congrArg Subtype.val e.symm)
  have he : Poly.send i c ^ 2 = 0 := by
    rw [pow_two]; by_contra hn
    obtain ⟨s,h₁,h₂⟩ := merges_of_tagged_mul hn
    obtain ⟨j,hj⟩ := h
    exact disjoint_left.mp h₁ hj hj
  rw [← exp_eq (Poly.send i c) (by simp [ht]), IsNilpotent.exp_eq_sum he]
  simp [sum_range_succ]

lemma pass_sum {α : Type*} (s : Finset α) (tag : α → R.Mode) (h : ∀ i∈s,(tag i).val.Nonempty) (f : α → ℂ) :
    Poly.pass (∑ i∈s,Poly.send (tag i) (f i)) = ∏ i∈s,(1+Poly.send (tag i) (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (pass_zero (R:=R))
  | insert i s hi ih =>
    have ht j (hj : j ∈ insert i s) : R.quiet ≠ tag j :=
      fun e => (h _ hj).ne_empty (congrArg Subtype.val e.symm)
    rw [sum_insert hi,prod_insert hi,pass_add (by simp [ht i (mem_insert_self ..)]) (by
      rw [Poly.part_sum]; exact sum_eq_zero fun j hj => by simp [ht j (mem_insert_of_mem hj)]),
      pass_send (h _ (mem_insert_self ..)),ih (fun i hi => h _ (mem_insert_of_mem hi))]
end Exp

section Log
variable [Fintype V]

private def vanishing (x : Poly R) (k : ℕ) := ∀ s : R.Mode, s.val.card ≤ k → x.part s=0
omit [Fintype V] in
private lemma vanish_zero {x : Poly R} (h : x.part R.quiet = 0) : vanishing x 0 := by
  intro s hs
  have he : s = R.quiet := Subtype.ext (card_eq_zero.mp (Nat.eq_zero_of_le_zero hs))
  rw [he,h]

omit [Fintype V] in
private lemma vanish_mul {x y : Poly R} {k : ℕ} (h : vanishing x k) (he : y.part R.quiet=0) :
    vanishing (x*y) (k+1) := by
  intro s hs
  rw [Poly.part_mul]; refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => ?_
  split
  next hM =>
    by_cases hj : j.val=∅
    · rw [show j=R.quiet from Subtype.ext hj,he,mul_zero]
    have hc := card_pos.mpr (nonempty_iff_ne_empty.mpr hj)
    rw [← hM.2,card_union_of_disjoint hM.1] at hs
    rw [h i (by omega),zero_mul]
  rfl

private lemma vanish_pass {x : Poly R} {k : ℕ} (h : vanishing x k) :
    vanishing (Poly.pass x-1-x) (k+1) := by
  have h0 := h R.quiet (by simp [Census.quiet])
  have ht (i : ℕ) (hi : 2 ≤ i) : vanishing (x^i) (k+1) := by
    induction i,hi using Nat.le_induction with
    | base => rw [pow_two]; exact vanish_mul h h0
    | succ i hi ih =>
      rw [pow_succ]; exact vanish_mul (fun s hs => ih s (hs.trans k.le_succ)) h0
  intro s hs
  rw [part_sub,part_sub,Poly.pass,Poly.part_sum, ← sum_erase_add (range (Fintype.card V+1)) _ (a:=0) (by simp),
    sum_eq_single 1]
  · simp
  · intro j hj hne
    have hj' : 2 ≤ j := by simp at hj; omega
    rw [Poly.part_smul, ht j hj' s hs,mul_zero]
  intro hj
  have hz : Fintype.card V = 0 := by simpa using hj
  rw [Poly.part_smul,pow_one,h s (by have := s.val.card_le_univ; omega),mul_zero]

private lemma improved {x y : Poly R} {k : ℕ} (hx : x.part R.quiet=0) (h : vanishing y k) :
    vanishing (Poly.pass (x+y)-Poly.pass x-y) (k+1) := by
  let z := Poly.pass y-1-y
  have hz : vanishing z (k+1) := vanish_pass h
  have hv := h R.quiet (by simp [Census.quiet])
  rw [pass_add hx hv]
  have hy : (Poly.pass x - 1).part R.quiet=0 := by simp [part_sub,Poly.pass_part x hx]
  rw [show Poly.pass x * Poly.pass y - Poly.pass x - y = z+(y*(Poly.pass x-1))+(z*(Poly.pass x-1)) by unfold z; ring]
  intro s hs
  simp [hz s hs,vanish_mul h hy s hs,vanish_mul (k:=k) (fun s H => hz s (H.trans k.le_succ)) hy s hs]

def iteration (x : Poly R) : ℕ → Poly R
  | 0 => 0
  | k+1 => iteration x k + (x-Poly.pass (iteration x k))

private lemma convergence {x : Poly R} (h : x.part R.quiet=1) (k : ℕ) :
    (iteration x k).part R.quiet=0 ∧ vanishing (x-Poly.pass (iteration x k)) k := by
  induction k with
  | zero => exact ⟨rfl,vanish_zero (by simp [iteration,pass_zero,part_sub,h])⟩
  | succ k ih =>
    let y := iteration x k
    let z := x-Poly.pass y
    have hz : vanishing z k := ih.2
    have he := hz R.quiet (by simp [Census.quiet])
    refine ⟨show (y+z).part _ = _ by simp [ih.1,he,y], ?_⟩
    have ht := improved ih.1 hz
    rw [iteration,show x-Poly.pass (y+z) = -(Poly.pass (y+z)-Poly.pass y-z) by unfold z; abel]
    exact fun s hs => by rw [Poly.part_neg, ht s hs, neg_zero]

def connected (x : Poly R) : Poly R := iteration x (Fintype.card V)

lemma connected_quiet {x : Poly R} (h : x.part R.quiet=1) : (connected x).part R.quiet=0 :=
  (convergence h _).1

lemma pass_connected {x : Poly R} (h : x.part R.quiet=1) : Poly.pass (connected x) = x := by
  ext i
  have he := (convergence h (Fintype.card V)).2 i i.val.card_le_univ
  exact (eq_of_sub_eq_zero he).symm

lemma pass_inj {x y : Poly R} (hx : x.part R.quiet=0) (hy : y.part R.quiet=0)
    (he : Poly.pass x = Poly.pass y) : x=y := by
  have h (k : ℕ) : vanishing (y-x) k := by
    induction k with
    | zero => exact vanish_zero (by rw [part_sub,hx,hy,sub_self])
    | succ k ih =>
      have ht := improved hx ih
      rw [add_sub_cancel, he, sub_self, zero_sub] at ht
      intro s hs; simpa only [Poly.part_neg,neg_eq_zero] using ht s hs
  ext i; exact (eq_of_sub_eq_zero (h (Fintype.card V) i i.val.card_le_univ)).symm



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞} {F : E → Poly R}

omit [Fintype V] in
private lemma contDiff_mul_part {H : E → Poly R}
    (hf : ∀ i, ContDiff ℝ k (fun x => (F x).part i)) (hh : ∀ i, ContDiff ℝ k (fun x => (H x).part i))
    (i : R.Mode) : ContDiff ℝ k (fun x => (F x * H x).part i) := by
  simp only [Poly.part_mul]
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  split
  · exact (hf i).mul (hh j)
  exact contDiff_const

lemma contDiff_pass (hf : ∀ i, ContDiff ℝ k (fun x => (F x).part i)) (i : R.Mode) :
    ContDiff ℝ k (fun x => (Poly.pass (F x)).part i) := by
  have hh (n : ℕ) (j : R.Mode) : ContDiff ℝ k (fun x => (F x ^ n).part j) := by
    induction n generalizing j with
    | zero => simp only [pow_zero]; exact contDiff_const
    | succ n ih => simp only [pow_succ]; exact contDiff_mul_part ih hf j
  simp only [Poly.pass,Poly.part_sum,Poly.part_smul]
  exact ContDiff.sum fun j _ => contDiff_const.mul (hh j i)

lemma contDiff_connected (hf : ∀ i, ContDiff ℝ k (fun x => (F x).part i)) (i : R.Mode) :
    ContDiff ℝ k (fun x => (connected (F x)).part i) := by
  have hh (n : ℕ) (j : R.Mode) : ContDiff ℝ k (fun x => (iteration (F x) n).part j) := by
    induction n generalizing j with
    | zero => exact contDiff_const
    | succ n ih => simp only [iteration,Poly.part_plus,part_sub]; exact (ih j).add ((hf j).sub (contDiff_pass ih j))
  exact hh _ _
end Log
end YM.Extra.Trajectories
