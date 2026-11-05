import YM.Next.WARD_BIN.Crest

/-!
# The actual first-order restrictions

These are reindexed Coefficient choices at all ancestors of all levels. No
estimating singleton modes by replacing with new support presentations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Crest
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V] {R : Rep G n} {r : Census V} {u v c d : ℝ} {W : V→ℝ}

omit [Fintype V] in
lemma fire_if (T S : r.Mode) (j : V) : Poly.merges T S (r.fire j) ↔ T=r.fire j ∧ S=r.quiet ∨ T=r.quiet ∧ S=r.fire j := by
  constructor
  · intro H
    have hp (T : r.Mode) (h : T.val⊆{j}) : T=r.quiet ∨ T=r.fire j := by rcases subset_singleton_iff.mp h with h|h; exact Or.inl (Subtype.ext h); exact Or.inr (Subtype.ext h)
    have hq : T.val∪S.val={j} := H.2
    rcases hp T (hq ▸ Finset.subset_union_left) with h|h
    · subst T; rw [Poly.vacuum] at H; exact Or.inr ⟨rfl,H⟩
    rcases hp S (hq ▸ Finset.subset_union_right) with he|he
    · exact Or.inl ⟨h,he⟩
    have hf : Disjoint ({j}: Finset V) {j} := show Disjoint (r.fire j).val (r.fire j).val from by simpa only [h,he] using! H.1
    simp at hf
  rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩); rw [Poly.wind]; exact (Poly.vacuum ..).mpr rfl
  exact (Poly.vacuum ..).mpr rfl
omit [Fintype V] in
lemma fire_mul (p q : Poly r) (j : V) : (p*q).part (r.fire j) = p.part r.quiet * q.part (r.fire j)+p.part (r.fire j)*q.part r.quiet := by
  rw [Poly.part_mul]
  let f (x y : r.Mode) := if Poly.merges x y (r.fire j) then p.part x * q.part y else 0
  have he (x y) : f x y=(if x=r.quiet ∧ y=r.fire j then p.part x*q.part y else 0)+(if x=r.fire j ∧ y=r.quiet then p.part x*q.part y else 0) := by
    by_cases h : x=r.quiet <;> by_cases hx : y=r.quiet
    · subst x y; simp [f,(r.fire_hot j).symm]
    · subst x; simp [f,(r.fire_hot j).symm]
    · subst y; simp [f,Poly.wind x r.quiet,h]
    have hh : ¬Poly.merges x y (r.fire j) := by simp [fire_if,h,hx]
    simp [f,hx,h,hh]
  change ∑ x,∑ y, f x y= _; simp_rw [he,sum_add_distrib]; simp [ite_and]
omit [Fintype V] in
lemma quiet_prod' {X : Type*} (f : X → Poly r) (s : Finset X) : (∏ i∈s,f i).part r.quiet=∏ i∈s,(f i).part r.quiet := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi h => rw [prod_insert hi,prod_insert hi, Poly.quiet_mul,h]
omit [Fintype V] in
lemma fire_prod {X : Type*} [DecidableEq X] (f : X → Poly r) (j : V) (T : Finset X) :
    (∏ i∈T,f i).part (r.fire j) = ∑ i∈T,(f i).part (r.fire j)*∏ k∈T.erase i,(f k).part r.quiet := by
  induction T using Finset.induction_on with
  | empty => simp [r.fire_hot]
  | insert i t hi h =>
    rw [prod_insert hi,sum_insert hi,fire_mul,quiet_prod',h,mul_sum,erase_insert hi, add_comm _ ((f i).part (r.fire j)*_)]; congr 1
    exact sum_congr rfl fun k hk => by
      have hh : k≠i := fun H => hi (H ▸ hk)
      rw [erase_insert_of_ne hh.symm, prod_insert (fun H => hi (mem_of_mem_erase H))]; ring


variable {Q : V → Rib G n} {C : Crest G n r} {δ w : ℝ}


lemma quiet_extra (A : Bands r R) (h : A.Active) (hr : A.Radial W u v c d) (U) : (A.extra U).part r.quiet=0 := by
  have H : ∀ j,(A.ray j U).part r.quiet=0 := fun j => by rw [Bands.ray,Poly.part_send,if_neg (fun H => (h.proper j).ne_empty (congr_arg Subtype.val H.symm))]
  rw [Bands.extra,Poly.part_plus,Poly.part_sum,Poly.share (A.bulkBound h hr U).1]; simp_rw [H]; simp [fun i => (r.fire_hot i).symm]

omit [Fintype V] in
lemma distant (i : V) (p : r.Mode) (h : 2 ≤ p.val.card) : r.fire i ≠ p := fun H => by rw [← H] at h; simp [Census.fire] at h

omit [Fintype V] [DecidableEq V] in
lemma fire_sum {f : V×ℕ⊕ℕ→ℂ} (i : V) (hp : Summable f) (hv : ∀ j,f (.inr j)=0) (hh : ∀ j,j ≠ i → ∀ x,f (.inl (j,x))=0) :
    ∑' p,f p=∑' b : ℕ,f (.inl (i,b)) := by
  have hX : Summable (f ∘ Sum.inl) := hp.comp_injective Sum.inl_injective
  rw [Summable.tsum_sum hX (hp.comp_injective Sum.inr_injective)]; simp_rw [hv]; rw [tsum_zero,add_zero]
  change ∑' p,(f ∘ Sum.inl) p=_
  rw [hX.tsum_prod,tsum_eq_single i]; rfl
  intro k hk; simp only [comp_apply,hh k hk,tsum_zero]
lemma fire_extra (h : ∀ i,(Q i).Pitched R) (hf : C.Green R fun i => (Q i).root) (hr : (meld Q C R).Radial W u v c d) (i : V) (U) :
    ((meld Q C R).extra U).part (r.fire i)=(Q i).fares R U := by
  let A := meld Q C R
  have he := (A.bulkBound (C.joined h hf) hr U).1
  rw [Bands.extra,Poly.part_plus,Poly.part_sum,Poly.share he]
  simp only [Poly.part_send,r.fire_inj,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  unfold Rib.fares; refine congr_arg ((Q i).head + ·) ?_
  let f (k : (V×ℕ⊕ℕ)) := (A.ray (enr V k) U).part (r.fire i)
  have hX : Summable (fun k : ℕ => (A.ray k U).part (r.fire i)) := (Poly.get (r.fire i)).summable (f:=fun k => A.ray k U) he
  have hp : Summable f := (Equiv.summable_iff (enr V) (f:=fun k => (A.ray k U).part (r.fire i))).mpr hX
  have hv (b : ℕ) : f (Sum.inr b)=0 := by simp only [f,A,Bands.ray,meld,Equiv.symm_apply_apply,Sum.elim_inr,Poly.part_send,if_neg (distant i (C.aims b) (hf.loaded b))]
  have hm (j : V) (b : ℕ) : f (.inl (j,b))= if i=j then masked R.p.threshold ((Q j).annals b) ((Q j).body b) U else 0 := by
    simp [f,A,Bands.ray,meld]
  calc
    _ = ∑' p,f p := (Equiv.tsum_eq (enr V) (fun k => (A.ray k U).part (r.fire i))).symm
    _ = ∑' b,f (.inl (i,b)) := fire_sum i hp hv (fun k h l => by rw [hm k l,if_neg h.symm])
    _ = _ := tsum_congr fun b => by rw [hm,if_pos rfl]

end YM.WardBin.Crest
