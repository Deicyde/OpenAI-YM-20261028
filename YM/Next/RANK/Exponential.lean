import YM.Marker.Truncated

/-!
# Connected vs total moments in the commuting marker algebra

Fix a finite family of slots. Use zero marker weights separately as quantum
vacuum; `Expands C F` means simply `C` is the unique connected polynomial of
`F` (F has constant coefficient one), by the finite exponential in this
marker algebra. The identities here are before any integral/copy estimate. They
honour the commuting square-zero convention even for higher arity.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Exponential
open Marker Finset
open scoped BigOperators Pointwise

variable {V : Type*} [DecidableEq V] {R : Census V}

private def vanish (q : ℕ) (a : Poly R) := ∀ T : R.Mode,T.val.card < q → a.part T=0

private lemma vanish_add {p q : ℕ} {a b : Poly R} (hx : vanish p a) (hy : vanish q b) : vanish (p+q) (a*b) := by
  intro T ht; rw [Poly.part_mul]
  apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _
  split_ifs with h
  · rcases h with ⟨h₁,h₂⟩
    by_cases hi : i.val.card<p
    · rw [hx i hi,zero_mul]
    rw [hy j (by rw [← h₂,card_union_of_disjoint h₁] at ht;omega),mul_zero]
  rfl
private lemma vanish_zero (a : Poly R) : vanish 0 a := fun _ hx => False.elim (Nat.not_lt_zero _ hx)
private lemma vanish_one {a : Poly R} (ha : a.part R.quiet=0) : vanish 1 a := by
  intro i hi; exact (show R.quiet=i from Subtype.ext (card_eq_zero.mp (show i.val.card=0 by omega)).symm) ▸ ha
private lemma vanish_pow {q} {a : Poly R} (h : vanish q a) : ∀ p : ℕ,vanish (q*p) (a^p)
  | 0 => by rw [Nat.mul_zero]; exact vanish_zero _
  | p+1 => by rw [Nat.mul_succ, pow_succ]; exact vanish_add (vanish_pow h p) h

@[simp] lemma part_sub (a b : Poly R) (i : R.Mode) : (a-b).part i=a.part i-b.part i := rfl

variable [Fintype V]

private def term (x : Poly R) (n : ℕ) := (n.factorial:ℂ)⁻¹ • x^n
lemma pass_extend {x : Poly R} (ht : x.part R.quiet=0) (n) (hn : Fintype.card V≤n) : Poly.pass x =
    ∑ i∈ Finset.range (n+1),(i.factorial:ℂ)⁻¹ • x^i := by
  apply sum_subset (Finset.range_mono (show Fintype.card V+1≤n+1 by omega))
  intro i _ hi; rw [Poly.stops x ht i (by simp at hi; exact hi),smul_zero]

@[simp] lemma pass_zero : Poly.pass (0:Poly R)=1 := by
  unfold Poly.pass
  rw [sum_eq_single 0]
  · simp
  · intro b _ h; rw [zero_pow h,smul_zero]
  simp

theorem pass_add (x y : Poly R) (hx : x.part R.quiet=0) (hy : y.part R.quiet=0) :
    Poly.pass (x+y) = Poly.pass x * Poly.pass y := by
  let p := term x
  let q := term y
  have he (n : ℕ) : term (x+y) n = ∑ z ∈ Finset.antidiagonal n,p z.1 * q z.2 := by
    unfold p q term
    rw [(Commute.all x y).add_pow' n,Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hl := Finset.mem_antidiagonal.mp hi
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_mul_smul_comm, ← hl, Nat.cast_add_choose, hl]
    field_simp [n.factorial_ne_zero]
  have h (i j : ℕ) (ht : Fintype.card V < i+j) : p i*q j=0 := by
    have hr := vanish_add (vanish_pow (vanish_one hx) i) (vanish_pow (vanish_one hy) j)
    unfold p q term
    rw [smul_mul_smul_comm,show x^i*y^j=0 from ?_,smul_zero]
    ext T; rw [Poly.part_nil,hr T (by simpa using lt_of_le_of_lt (card_le_univ _) ht)]
  let A := Finset.range (Fintype.card V + 1)
  let I := fun (x : ℕ × ℕ) => p x.1*q x.2
  let B := A.biUnion Finset.antidiagonal
  have hf : B ⊆ A ×ˢ A := by
    refine Finset.biUnion_subset.mpr ?_
    intro i hi z hz; unfold A at *; rw [Finset.mem_range] at hi;rw [Finset.mem_antidiagonal] at hz
    exact Finset.mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
  have hv : (∑ i∈B,I i)=∑ i∈ A ×ˢ A,I i := by
    refine sum_subset hf ?_
    rintro ⟨i,j⟩ _ H
    apply h
    by_contra! hh; exact H (mem_biUnion.mpr ⟨i+j,mem_range.mpr (by omega),Finset.mem_antidiagonal.mpr rfl⟩)
  have hg : (A:Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
    intro i _ j _ he; exact Finset.disjoint_left.mpr fun k hk he' => he (((Finset.mem_antidiagonal.mp hk).symm).trans (Finset.mem_antidiagonal.mp he'))
  rw [show (∑ i∈B,I i) = ∑ j∈A, ∑ i ∈ Finset.antidiagonal j,I i from Finset.sum_biUnion hg, Finset.sum_product] at hv
  change (∑ i∈A,term (x+y) i)=(∑ i∈A,p i)*(∑ i∈A,q i)
  rw [sum_mul_sum]; simp_rw [he]; exact hv

lemma pass_neg (x : Poly R) (hx : x.part R.quiet=0) : Poly.pass (-x)*Poly.pass x=1 := by rw [← pass_add _ _ (by simp [hx]) hx, neg_add_cancel, pass_zero]

lemma pass_sum {W : Type*} (s : Finset W) (f : W → Poly R) (h : ∀ i∈s,(f i).part R.quiet=0) :
    Poly.pass (∑ i∈s,f i)= ∏ i∈s,Poly.pass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have he : ∀ i∈t,(f i).part R.quiet=0 := fun k hk => h k (by simp [hk])
    rw [sum_insert hi, prod_insert hi, pass_add,ih he]; exact h i (mem_insert_self ..)
    rw [Poly.part_sum]; exact sum_eq_zero he

-- For the logarithm we use the triangularity rather than formal differentiation.
private lemma pass_linear (x : Poly R) {m : ℕ} (hm : 0<m) (hx : vanish m x) (i : R.Mode)
    (hi : i.val.card < m+1) : (Poly.pass x).part i = (1:Poly R).part i+x.part i := by
  let n := Fintype.card V
  rw [pass_extend (hx _ (show Finset.card _ < _ from by simpa [Census.quiet])) (n+1) (by dsimp [n]; omega),Poly.part_sum]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  change (∑ j∈ Finset.range n,(term x (j+1+1)).part i)+(term x 1).part i+(term x 0).part i = _
  have he j : (term x (j+1+1)).part i=0 := by
    have h : m*(j+1+1)≥m+1 := by nlinarith
    rw [term, Poly.part_smul,vanish_pow hx (j+1+1) i (lt_of_lt_of_le hi h),mul_zero]
  simp_rw [he,Finset.sum_const_zero,zero_add]
  simp [term, add_comm]

private lemma fresh (a x : Poly R) (ha : a.part R.quiet=0) {m : ℕ} (hp : 0<m)
    (hx : vanish m x) : vanish (m+1) (Poly.pass (a+x) - (Poly.pass a + x)) := by
  let u := Poly.pass a - 1
  let v := Poly.pass x - (1+x)
  have hu : vanish 1 u := vanish_one (by simp only [u, part_sub,Poly.pass_part a ha,Poly.one_part]; simp)
  have hv : vanish (m+1) v := fun i hi => by simp only [v,part_sub,pass_linear x hp hx i hi,Poly.part_plus,sub_self]
  have hE : Poly.pass (a+x) - (Poly.pass a+x) = u*x + (Poly.pass a)*v := by
    rw [pass_add a x ha (hx _ (by simpa [Census.quiet]))]; dsimp [u,v]; ring
  intro i hi; rw [hE,Poly.part_plus,vanish_add hu hx i (by omega),vanish_add (vanish_zero _) hv i (by omega), add_zero]

/-- In marker algebra use unique logarithm with vanishing vacuum value. -/
def Expands (C F : Poly R) : Prop := C.part R.quiet=0 ∧ Poly.pass C=F

-- A continuous extension formula for the cumulants from coordinates (when F.part quiet=1).

def roll (F : Poly R) : ℕ → Poly R
  | 0 => 0
  | i+1 => roll F i+(F-Poly.pass (roll F i))
lemma rolls (F : Poly R) (hf : F.part R.quiet=1) : Expands (roll F (Fintype.card V)) F := by
  have h (n : ℕ) : (roll F n).part R.quiet=0 ∧ vanish (n+1) (F-Poly.pass (roll F n)) := by
    induction n with
    | zero => exact ⟨rfl,vanish_one (by simp [hf,roll])⟩
    | succ n ih =>
      let C := roll F n
      obtain ⟨hx,H⟩ := ih
      let x := F-Poly.pass C
      have hz : x.part R.quiet=0 := H _ (by simp [Census.quiet])
      rw [roll]; refine ⟨by rw [Poly.part_plus,hx,hz,zero_add],fun i hi => ?_⟩
      have he := fresh C x hx (Nat.zero_lt_succ _) H i hi
      have hh : F=Poly.pass C + x := by dsimp [x]; abel
      rw [← hh,part_sub] at he
      exact sub_eq_zero.mpr (sub_eq_zero.mp he).symm
  obtain ⟨hp,H⟩ := h (Fintype.card V)
  refine ⟨hp,?_⟩; ext i
  have he := H i (Nat.lt_succ_of_le (card_le_univ _)); rw [part_sub] at he; exact (sub_eq_zero.mp he).symm

lemma roll_cont (i : ℕ) : Continuous fun F : Poly R => roll F i := by
  induction i with
  | zero => exact continuous_const
  | succ i H =>
    simp_rw [roll]; apply H.add; refine continuous_id.sub ?_
    unfold Poly.pass; exact continuous_finsetSum _ fun j _ => (H.pow j).const_smul ((j.factorial:ℂ)⁻¹)

lemma exists_expands (F : Poly R) (hf : F.part R.quiet=1) : ∃ C : Poly R, Expands C F :=
  ⟨_,rolls F hf⟩

lemma Expands.uniq {C D F : Poly R} (h : Expands C F) (hx : Expands D F) : C=D := by
  let p := C+ -D
  have ht : p.part R.quiet=0 := by simp [p,h.1,hx.1]
  have he : Poly.pass p=1 := by
    dsimp only [p]; rw [pass_add _ _ h.1 (by simp [hx.1]),h.2,← hx.2, mul_comm]; exact pass_neg _ hx.1
  have H (m : ℕ) : vanish (m+1) p := by
    induction m with
    | zero => exact vanish_one ht
    | succ k ih =>
      intro i hi
      have h := pass_linear p (Nat.zero_lt_succ _) ih i hi
      rw [he] at h; exact add_left_cancel (h.symm.trans (add_zero _).symm)
  have hh : p=0 := Poly.ext fun i => H (Fintype.card V) i (Nat.lt_succ_of_le (card_le_univ _))
  exact sub_eq_zero.mp (by rwa [sub_eq_add_neg])

/-- Only for vacuum coefficient one. -/
def connected (F : Poly R) (hf : F.part R.quiet=1) := (exists_expands F hf).choose

lemma connected_spec (F : Poly R) (hf : F.part R.quiet=1) : Expands (connected F hf) F :=
  (exists_expands F hf).choose_spec

/-- Remove the free total moments via exp of *minus* the connected ones; returns exact
moments, not norm estimates. Keep constant = 1 when present. -/
lemma correct {D F : Poly R} (h : Expands D F) (P : Poly R) : F*(Poly.pass (-D)*P)=P := by
  rw [← mul_assoc,← h.2,mul_comm (Poly.pass D),pass_neg _ h.1,one_mul]

end YM.Next.Rank.Exponential
