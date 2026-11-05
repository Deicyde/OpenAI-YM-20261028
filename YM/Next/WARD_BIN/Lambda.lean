import YM.Next.WARD_BIN.Crest
/-!
# Marker algebra expansion for cutoff

Coefficient identities for EACH distributed marker set. No hidden factorials,
no summability via size estimates on powers of leading radius. FULL census.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Lambda
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay Crest
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {r : Census V} {G : Gauge} {n : Side}

def fuse (i : V) (x : ℂ) : Poly (Full V) := Poly.send ((Full V).fire i) x


omit [Fintype V] in
lemma parades (a b c : r.Mode) (h : Poly.merges a b c) (x y : ℂ) :
    Poly.send a x * Poly.send b y= Poly.send c (x*y) := by
  ext1 i
  rw [show (_*_ : Poly r)=Poly.prod (Poly.send a x) (Poly.send b y) from rfl,Poly.cart,Poly.part_send]
  have he : Poly.merges a b i ↔ i=c := ⟨fun H => Subtype.ext (H.2.symm.trans h.2),fun H => H.symm ▸ h⟩
  simp only [he]
omit [Fintype V] in
lemma scalar_mul (x : r.Mode) (a b) : Poly.send x a* Poly.send r.quiet b=Poly.send x (a*b) := parades x r.quiet x ((Poly.wind ..).mpr ((Poly.vacuum ..).mpr rfl)) a b
lemma parade (T : Finset V) (f : V→ℂ) : ∏ i∈T,fuse i (f i)=Poly.send (chest T) (∏ i∈T,f i) := by
  induction T using Finset.induction_on with
  | empty => rw [prod_empty,prod_empty]; rfl
  | insert i t hi ih =>
    rw [prod_insert hi,prod_insert hi,ih]; apply parades
    exact ⟨Finset.disjoint_singleton_left.mpr hi,singleton_union _ _⟩
lemma expend (f : V→ℂ) (T : Mode V) : (∏ i,(fuse i (f i)+1)).part T=∏ i∈T.val,f i := by
  rw [prod_add_one, Poly.part_sum]; simp_rw [parade,Poly.part_send]
  rw [sum_eq_single T.val] -- in powerset
  · exact if_pos rfl
  · exact fun i _ hi => if_neg fun H => hi (congr_arg Subtype.val H).symm
  simp
lemma touching (T : Mode V) (j : V) (hp : j∈T.val) : Poly.merges (chest (T.val.erase j)) ((Full V).fire j) T := by
  refine ⟨Finset.disjoint_singleton_right.mpr (notMem_erase _ _),?_⟩
  change T.val.erase j∪{j}=T.val; rw [union_comm,singleton_union,insert_erase hp]
lemma unmerged (T : Mode V) (j : V) (b : Mode V) : Poly.merges b ((Full V).fire j) T →
    j∈T.val ∧ chest (T.val.erase j)=b := by
  rintro ⟨h,hH⟩; rw [← hH]
  refine ⟨mem_union_right _ (mem_singleton_self _),Subtype.ext ?_⟩
  change (b.val ∪ {j}).erase j = b.val; rw [union_comm,singleton_union,erase_insert]
  exact Finset.disjoint_singleton_right.mp h
lemma fused (T : Mode V) (j : V) (a : Poly (Full V)) (x : ℂ) : (a*fuse j x).part T=
    if j∈T.val then a.part (chest (T.val.erase j))*x else 0 := by
  have he (c) : (∑ y, if Poly.merges c y T then a.part c*(fuse j x).part y else 0) =
      if Poly.merges c ((Full V).fire j) T then a.part c*x else 0 := by
    rw [sum_eq_single ((Full V).fire j)]; simp [fuse]
    · intro b _ hb; split_ifs; rw [fuse,Poly.part_send,if_neg hb,mul_zero]; rfl
    simp
  rw [Poly.part_mul]; simp_rw [he]
  split_ifs with h
  · rw [sum_eq_single (chest (T.val.erase j)), if_pos (touching T j h)]
    · intro b _ hb; exact if_neg (fun H => hb (unmerged T j b H).2.symm)
    simp
  exact sum_eq_zero fun b _ => if_neg fun H => h (unmerged T j b H).1
lemma pressed (T : Mode V) (f : V→ℂ) : ∀ k, ((∑ i,fuse i (f i))^k).part T=
    if k=T.val.card then (k.factorial:ℂ)*∏ i∈T.val,f i else 0 := by
  intro k; induction k generalizing T with
  | zero =>
    by_cases h : T=(Full V).quiet
    · subst T; simp [Census.quiet]
    have hv : T.val ≠ ∅ := fun H => h (Subtype.ext H); have hp : T.val.card≠0 := mt Finset.card_eq_zero.mp hv
    simp [hp.symm,h]
  | succ k IH =>
    rw [pow_succ,mul_sum,Poly.part_sum]; simp_rw [fused]; rw [← sum_filter]; split_ifs with h
    · simp only [Finset.filter_mem_eq_inter,univ_inter]
      calc
        _ = ∑ _i∈ T.val, (k.factorial:ℂ)*∏ i∈T.val,f i := sum_congr rfl fun i hi => by
          rw [IH,show (chest (T.val.erase i)).val=_ from (rfl : _=(T.val.erase i)), if_pos (show k=(T.val.erase i).card by rw [card_erase_of_mem hi, ← h]; omega)]
          rw [show _*(∏ l∈T.val.erase i,_) * _=(k.factorial:ℂ)*((∏ l∈T.val.erase i,f l)*f i) from mul_assoc .., prod_erase_mul _ f hi]
        _ = _ := by rw [sum_const,nsmul_eq_mul,← h,Nat.factorial_succ, Nat.cast_mul,mul_assoc]
    refine sum_eq_zero fun i hi => ?_
    rw [IH,if_neg ?_,zero_mul]; intro H; apply h; have hh := (mem_filter.mp hi).2
    change k=(T.val.erase i).card at H
    rw [card_erase_of_mem hh] at H; have he := card_pos.mpr ⟨i,hh⟩; omega

lemma passion (f : V→ℂ) : Poly.pass (∑ i,fuse i (f i))=∏ i, (fuse i (f i)+1) := by
  ext1 y
  rw [Poly.pass,Poly.part_sum]; simp_rw [Poly.part_smul,pressed]; rw [expend,sum_eq_single y.val.card]
  · rw [if_pos rfl,inv_mul_cancel_left₀]; exact_mod_cast Nat.factorial_ne_zero _
  · exact fun i _ hi => by rw [if_neg hi,mul_zero]
  simp [card_le_univ]

end YM.WardBin.Lambda
