import YM.SectorNext.RECONNECTED_LOCALITY.Fleet

set_option warningAsError false

/-!
# Mayer variants with addresses intact

Exclusive choices among h variants of one
parent even for infinite alphabets (in E the run of telescope variants would
only be finite at each parent). Use pointwise summability of the actual variant
values, not assuming that their integrated series even exists. An unselected
address contributes one, not tagged with irrelevant choices. No reusing a
non-table address solely because a different cut sector made its value nonzero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Optional
open Words Fleet Function Filter Finset
open scoped Classical

variable {ι par : Type*}

/-- helper for countable trees too. Exact value (and by norm also absolute).
No countability class needed here (real unconditional sums). -/
private theorem numbered {n : ℕ} {E : Fin n → Type*} (f : ∀ i,E i → ℝ)
    (he : ∀ i,Summable (f i)) :
    HasSum (fun (x : ∀ i,E i) => ∏ i,f i (x i)) (∏ i,∑' j,f i j) := by
  induction n with
  | zero =>
    let F := fun (x : ∀ i,E i) => ∏ i,f i (x i)
    haveI : Unique (∀ i,E i) := inferInstance
    simpa only [F,prod_of_isEmpty,Fintype.sum_unique] using (hasSum_fintype F) -- adjust
  | succ n IH =>
    rw [Fin.prod_univ_succ]
    let G := fun (x : ∀ i : Fin n, E i.succ) => ∏ i,f i.succ (x i)
    have hh : HasSum G (∏ i : Fin n,∑' j,f i.succ j) := IH _ (fun i => he i.succ)
    have hp:= (he 0).hasSum.mul hh (summable_mul_of_summable_norm (he 0).norm hh.summable.norm)
    apply (Fin.consEquiv E).hasSum_iff.mp
    refine hp.congr_fun ?_
    rintro ⟨i,x⟩
    simp only [comp_apply,G, Fin.prod_univ_succ,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]


theorem series_prod [Fintype ι] {E : ι → Type*} (f : ∀ i,E i → ℝ) (he : ∀ i,Summable (f i)) :
    HasSum (fun (x : ∀ i,E i) => ∏ i,f i (x i)) (∏ i,∑' j,f i j) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (Equiv.piCongrLeft E e).hasSum_iff]
  simp_rw [comp_def,← e.prod_comp, Equiv.piCongrLeft_apply_apply]
  exact numbered _ fun i => he _

private abbrev Fiber (p : ι → par) (j : par) := {i // p i=j}

private def plants (p : ι → par) (t : Finset par) (x : ∀ i : ↥t,Fiber p i.val) : Finset ι :=
    t.attach.image fun i => (x i).val

private lemma places {p : ι → par} (t : Finset par) (x : ∀ i : ↥t,Fiber p i.val) : Injective fun i => (x i).val :=
  fun a b h => Subtype.ext ((x a).property.symm.trans ((congr_arg p h).trans (x b).property))

private lemma produces {p : ι → par} (t : Finset par) (x : ∀ i : ↥t,Fiber p i.val) : Fleet.pure p (plants p t x) ∧
    (plants p t x).image p=t := by
  constructor
  · intro i hi j hj hn
    obtain ⟨a,_,rfl⟩:=mem_image.mp hi; obtain ⟨b,_,rfl⟩:=mem_image.mp hj
    rw [(x b).property,(x a).property] at hn
    have he : b=a := Subtype.ext hn
    rw [he]
  · ext i
    simp only [plants,mem_image,mem_attach,true_and]
    constructor
    · rintro ⟨j,⟨q,rfl⟩,rfl⟩; rw [(x q).property]; exact q.property
    intro he
    exact ⟨_,⟨⟨i,he⟩,rfl⟩,(x _).property⟩

/-- Tuple of alternatives at t selected parents represents each such selection of variants once. -/
private def atParents (p : ι → par) (t : Finset par) :
    (∀ i : ↥t,Fiber p i.val) ≃ {b // Fleet.pure p b ∧ Finset.image p b=t} where
  toFun x := ⟨plants p t x, produces t x⟩
  invFun b := fun i =>
    have he : i.val ∈ Finset.image p b.val := by rw [b.property.2]; exact i.property
    ⟨(mem_image.mp he).choose,(mem_image.mp he).choose_spec.2⟩
  left_inv x := by
    funext i
    dsimp only
    generalize_proofs h
    apply Subtype.ext
    obtain ⟨q,_,hq⟩:=mem_image.mp h.choose_spec.1
    have he:= h.choose_spec.2
    rw [← hq,(x q).property] at he
    change h.choose = _
    exact hq.symm.trans (by rw [show q=i from Subtype.ext he])
  right_inv := by
    intro b; apply Subtype.ext; ext j
    simp only [plants, mem_image,mem_attach,true_and]
    constructor
    · rintro ⟨a,rfl⟩
      generalize_proofs h
      exact h.choose_spec.1
    intro hj
    have he : p j∈t := by rw [← b.property.2]; exact Finset.mem_image_of_mem p hj
    use ⟨_,he⟩
    generalize_proofs h
    exact b.property.1 j hj _ h.choose_spec.1 h.choose_spec.2

private lemma planted (p : ι → par) (t : Finset par) (f : ι → ℝ) (x : ∀ i : ↥t,Fiber p i.val) :
    (∏ i∈((atParents p t x).val),f i)=∏ i,f (x i).val := by
  change (∏ i∈(plants p t x),f i)=_
  rw [plants,prod_image (places t x).injOn]
  rfl

/-- Helpful for all primary reindexings; telescope along `s` (can be infinite map). -/
theorem group_by {f : ι → ℝ} (s : ι → par) (hf : Summable f) :
    Summable (fun i => ∑' j : Fiber s i,f j.val) ∧ ∑' i,f i = ∑' i,∑' j : Fiber s i,f j.val := by
  let E:=Equiv.sigmaFiberEquiv s
  have H := E.summable_iff.mpr hf
  exact ⟨H.sigma,(E.tsum_eq f).symm.trans H.tsum_sigma⟩

def subsetTerm (p : ι → par) (F : ι → ℝ) (w : Finset ι) : ℝ := if Fleet.pure p w then ∏ i∈w,F i else 0



def factors (p : ι → par) (F : ι → ℝ) (i : par) := 1+∑' j : Fiber p i,F j.val

theorem expanding (p : ι → par) {F : ι → ℝ} (hs : Summable F) :
    HasSum (subsetTerm p F) (∏' j,factors p F j) ∧ Multipliable (factors p F) := by
  let f i := ∑' j : Fiber p i,F j.val
  have hsum : Summable f := (group_by p hs).1
  refine ⟨?_,multipliable_one_add_of_summable hsum.norm⟩
  let T:=fun i : {s // Fleet.pure p s} => ∏ j∈i.val,F j
  have hT : Summable T := (summable_finsetProd_of_summable_norm hs.norm).comp_injective Subtype.val_injective
  let book := fun i : {s // Fleet.pure p s} => i.val.image p
  have ht (b) : (∑' j : Fiber book b,T j.val)=∏ i∈b,f i := by
    let e : {s : Finset ι // Fleet.pure p s ∧ Finset.image p s=b} ≃ Fiber book b :=
      { toFun := fun a => ⟨⟨a.val,a.property.1⟩, a.property.2⟩
        invFun := fun a => ⟨a.val.val,a.val.property,a.property⟩
        left_inv _:=rfl
        right_inv _:=rfl }
    have hq := (series_prod (E:=fun i : ↥b => Fiber p i.val) (fun _ j => F j.val) fun i => hs.comp_injective Subtype.val_injective).tsum_eq
    rw [← ((atParents p b).trans e).tsum_eq]
    rw [← prod_coe_sort b f,← hq]; exact tsum_congr (planted p b F)
  apply (hasSum_subtype_iff_of_support_subset (s:={s : Finset ι | Fleet.pure p s}) (f:=subsetTerm p F)
    (by intro i hi; exact of_not_not (fun hh => hi (if_neg hh)))).mp
  change HasSum (subsetTerm p F ∘ (Subtype.val : {s // Fleet.pure p s} → Finset ι)) _
  rw [show subsetTerm p F ∘ (Subtype.val : {s // Fleet.pure p s} → Finset ι)=T from funext fun i => if_pos i.property]
  apply hT.hasSum_iff.mpr
  rw [(group_by book hT).2]
  simp_rw [ht]
  exact (tprod_one_add (summable_finsetProd_of_summable_norm hsum.norm)).symm

end YM.SectorNext.Reconnect.Optional
