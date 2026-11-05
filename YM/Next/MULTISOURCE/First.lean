import YM.Next.MULTISOURCE.Evaluate

/-!
# Read one tangent exactly
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi
open RG Wilson Lattice Finset Marker
open scoped Topology BigOperators

variable {V : Type*} [DecidableEq V] {R : Census V}
variable {n : Side} {G : Gauge}

lemma merge_one (i : V) (x y : R.Mode) : Poly.merges x y (R.fire i) ↔
    (x=R.quiet ∧ y=R.fire i) ∨ (x=R.fire i ∧ y=R.quiet) := by
  constructor
  · rintro h
    by_cases hx : x=R.quiet
    · subst x; exact Or.inl ⟨rfl,Poly.vacuum y _ |>.1 h⟩
    right
    have he : x.val.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun H => hx (Subtype.ext H)
    have ht := card_pos.mpr he
    obtain ⟨H,hH⟩ := h
    have hw : x.val.card+y.val.card=1 := by rw [← card_union_of_disjoint H,hH]; exact card_singleton _
    have hy : y.val=∅ := card_eq_zero.mp (by omega)
    exact ⟨Subtype.ext (by simpa only [hy, union_empty] using hH), Subtype.ext hy⟩
  rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
  · simp
  rw [Poly.wind]; simp

lemma first_mul (a b : Poly R) (i : V) : (a*b).part (R.fire i) =
    a.part R.quiet*b.part (R.fire i)+a.part (R.fire i)*b.part R.quiet := by
  rw [Poly.part_mul]
  have hn := R.fire_hot i
  let f (x : R.Mode) := ∑ y, if Poly.merges x y (R.fire i) then a.part x*b.part y else 0
  change ∑ x,f x=_
  rw [← Finset.add_sum_erase _ f (mem_univ R.quiet), sum_eq_single (R.fire i) (s:=univ.erase R.quiet)]
  · unfold f; simp [merge_one, hn, Ne.symm hn]
  · intro x hx h
    unfold f; simp [merge_one,h,(mem_erase.mp hx).1]
  simp [hn]

lemma quiet_of_prod {I : Type*} (S : Finset I) (f : I → Poly R) :
    (∏ i∈S,f i).part R.quiet = ∏ i∈S,(f i).part R.quiet := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert i S h ih => rw [prod_insert h, prod_insert h,Poly.quiet_mul,ih]

lemma first_of_prod {I : Type*} [DecidableEq I] (S : Finset I) (f : I → Poly R) (j : V) :
    (∏ i∈S,f i).part (R.fire j) = ∑ i∈S,(f i).part (R.fire j)*∏ x∈S.erase i,(f x).part R.quiet := by
  induction S using Finset.induction with
  | empty => simp [R.fire_hot]
  | insert i S h ih =>
    rw [prod_insert h,first_mul,ih,quiet_of_prod,sum_insert h,erase_insert h,add_comm,mul_sum]
    congr 1
    refine sum_congr rfl fun p hp => ?_
    rw [Finset.erase_insert_of_ne (show i ≠ p from fun H => h (H ▸ hp)), prod_insert (fun H => h (mem_of_mem_erase H))]
    ring

lemma singleton_shards (i : V) (R : Census V) : shards R (R.fire i)={ (parts R).fire (Hot.one R i) } := by
  ext x
  simp only [shards,mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · intro h
    apply Subtype.ext
    change x.val={Hot.one R i}
    have hy : x.val.biUnion Hot.sites={i} := congrArg Subtype.val h
    have hf {b} (hb : b∈ x.val) : b = Hot.one R i := Hot.eq_of_sites (by
      change b.sites={i}; apply le_antisymm
      · intro j hj; rw [← hy]; exact mem_biUnion.mpr ⟨b,hb,hj⟩
      obtain ⟨v,hv⟩ := b.property
      have ht : v=i := Finset.mem_singleton.mp (hy ▸ mem_biUnion.mpr ⟨b,hb,hv⟩)
      rw [singleton_subset_iff]; rwa [← ht])
    apply eq_singleton_iff_unique_mem.mpr
    obtain ⟨b,hb,H⟩ := mem_biUnion.mp (by rw [hy]; simp : i∈ x.val.biUnion Hot.sites)
    exact ⟨hf hb ▸ hb, fun v hv => hf hv⟩
  rintro rfl; exact unionOf_single _

lemma singleton_blocks (i : V) (R : Census V) : blocksOf R (Hot.one R i)={Hot.one (parts R) (Hot.one R i)} := by
  ext x
  simp only [blocksOf,mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · intro h
    have ht : x.val ∈ shards R (R.fire i) := mem_filter.mpr ⟨mem_univ _, congrArg Subtype.val h⟩
    rw [singleton_shards] at ht; exact Subtype.ext (mem_singleton.mp ht)
  rintro rfl; rw [unionOfHot_one]

/-- Literal linearized density function (includes vacuum in zero sector). -/
def tangent (P : Rep G n) (D : Pulse G n) (U : Config G n) : ℂ :=
    (P.eval U:ℂ)*D.1 U + (Real.exp (P.exponent U):ℂ) *
      ∑ b∈Pack.clears (flags P.p.threshold U), ∑ i∈b,D.2 i U * ∏ v∈b.erase i, incumbent P U v

lemma tangent_scale (P : Rep G n) (D : Pulse G n) (z : ℂ) : tangent P (z • D) = z • tangent P D := by
  funext U
  simp only [tangent,Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_add]
  rw [mul_left_comm (↑(P.eval U):ℂ), mul_left_comm z (↑(Real.exp _):ℂ), Finset.mul_sum]
  simp_rw [Finset.mul_sum,mul_assoc]

variable [Fintype V]

lemma first_pass (i : V) (x : Poly R) (hx : x.part R.quiet=0) :
    (x.pass).part (R.fire i)=x.part (R.fire i) := by
  rw [Poly.pass,Poly.part_sum,sum_eq_single 1]
  · simp
  · intro y _ hy; rw [Poly.part_smul]
    by_cases h : y=0
    · subst y; simp [R.fire_hot]
    rw [Poly.high x hx _ _ (by simp only [Census.fire,card_singleton]; omega)]; ring
  haveI : Nonempty V := ⟨i⟩
  simp [Fintype.card_pos]

lemma first_jet {δ κ : ℝ} (P : Rep G n) (h : P.activities.Valid P.p δ κ) (D : V → Pulse G n) (R : Census V) (i : V) :
    jet P R D (R.fire i) = tangent P (D i) := by
  funext U
  simp only [jet,polar,composeAt,Poly.part_smul, first_mul, Poly.pass_part _ (lambda_quiet _),
    first_pass i _ (lambda_quiet _), Poly.part_sum, first_of_prod, quiet_of_prod, Poly.part_plus,
    lambda_quiet,lambda_part,Poly.part_send,R.fire_hot,↓reduceIte,zero_add,add_zero]
  rw [← real_book _ _ h]
  unfold tangent Rep.eval
  push_cast; ring

lemma firstMany {δ κ : ℝ} (P : Rep G n) (h : P.activities.Valid P.p δ κ) (D : Hot R → Pulse G n) (i : V) (U) :
    (many P R D U).part (R.fire i) = tangent P (D (Hot.one R i)) U := by
  rw [allJets, singleton_shards, Finset.sum_singleton, first_jet _ h]

lemma floor_part {δ κ : ℝ} (P : Rep G n) (U : Config G n) (h : P.activities.Valid P.p δ κ)
    (e : Poly R) (b : Pack n → Poly R) (he : e.part R.quiet=0) (ht : ∀ q, (b q).part R.quiet=0) :
    (composeAt P U e b).part R.quiet=(P.eval U:ℂ) := by
  unfold composeAt Rep.eval
  simp_rw [Poly.part_smul, Poly.quiet_mul, Poly.pass_part _ he, Poly.part_sum, quiet_of_prod,
    Poly.part_plus,ht,Poly.part_send, if_true, add_zero, one_mul]; rw [← real_book _ _ h, Complex.ofReal_mul]
end YM.Multi
