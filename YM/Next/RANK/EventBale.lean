import YM.Analysis.Polydisc
import YM.Next.RANK.EntryWord

/-!
# Addresses grouped by support and inventory

Take finite functions/groups by budget; within each support such a group
is mutually exclusive. Lean proof permits infinite input even at finite period
(historical formula); every use must exhibit Summable. No error from regrouping.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Baler
open Function Filter RG Lattice Wilson Finset MeasureTheory Relation Corona
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

variable {X : Type} [DecidableEq X] [Fintype X]
variable {α β : Type}

abbrev Crate (X : Type*) [DecidableEq X] := { s : Finset X × Finset X // s.2.Nonempty ∧ s.2 ⊆ s.1}

-- same crate u_i from whole source/ga object

def ripe (G : α → Crate X) (i : Finset α) (f : Finset X) :=
    (i:Set _).PairwiseDisjoint (fun j=> (G j).val.1) ∧ i.biUnion (fun j => (G j).val.2) = f

def fibres [DecidableEq β] (b : α→β) (i : Finset α) (j : Finset β) := (i:Set _).InjOn b ∧ image b i=j

omit [Fintype X] in
lemma picks (G : α→Crate X) (a : Finset α) (i : Finset X) :
    ripe G a i ↔ (fibres G a (a.image G) ∧ ripe id (a.image G) i) := by
  have he : a.biUnion (fun j => (G j).val.2)=(a.image G).biUnion (fun j=> j.val.2) := by
    ext b; constructor
    · intro hb; obtain ⟨c,hc,hp⟩:=mem_biUnion.mp hb; exact mem_biUnion.mpr ⟨G c,mem_image_of_mem _ hc,hp⟩
    intro hb; obtain ⟨c,hc,hp⟩:=mem_biUnion.mp hb; obtain ⟨c,hc,rfl⟩:=mem_image.mp hc; exact mem_biUnion.mpr ⟨c,(by aesop),hp⟩
  constructor
  · rintro ⟨h,H⟩
    refine ⟨⟨fun i hi j hj he=>?_ ,rfl⟩,fun i hi j hj Hp=>?_,he.symm.trans H⟩
    · by_contra hx; obtain ⟨c,hc⟩ := (G i).property.1; have hu := (G i).property.2 hc; exact disjoint_left.mp (h hi hj hx) hu (show c∈ (G j).val.1 from he ▸ hu)
    obtain ⟨i,ha,rfl⟩:=mem_image.mp hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hj
    apply h ha (show j∈a from by aesop); exact fun hh : i=j=>Hp (congr_arg G hh)
  rintro ⟨hp,h,H⟩; exact ⟨fun i hi j hj he => h (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) (hp.1.ne hi hj he),he.trans H⟩

section
variable {R : Type*} [CommSemiring R]
-- mapped set implies disjoint; projection of independent sum
private lemma one [DecidableEq β] (f : α→β) (P : α→R) (X : Finset α) (Y : Finset β) :
    ∏ y∈Y,(∑ i∈X.filter (fun i=> f i=y),P i) = ∑ i ∈ X.powerset.filter (fun i=> fibres f i Y),∏ j∈i,P j := by
  induction Y using Finset.induction_on with
  | empty =>
    have h : X.powerset.filter (fun i => fibres f i ∅) = {∅} := by
      ext i; simp [fibres]; by_cases h : i=∅<;>simp [h]
    simp [h]
  | @insert i s hi ih =>
    let A:= X.filter fun j=> f j=i
    let B:= X.powerset.filter (fun j=> fibres f j s)
    let Y:= X.powerset.filter (fun j=>fibres f j (insert i s))
    rw [prod_insert hi,ih,Finset.sum_mul_sum]; change ∑ j∈A,∑ k∈B,P j*_ = _
    have he (x : α × Finset α) (h : x ∈ A×ˢB) : f x.1=i ∧ x.1∉x.2 ∧ (∀ j ∈ x.2, f j≠i) ∧ (insert x.1 x.2 : Finset α)∈Y := by
      rcases x with ⟨x,b⟩; obtain ⟨ha,hb⟩:=mem_product.mp h
      obtain ⟨hx,hy⟩:=mem_filter.mp (show x∈A from ha); obtain ⟨hu,hv⟩:=mem_filter.mp (show b∈B from hb)
      obtain ⟨hT,hB⟩:=hv
      have hg j (hj:j∈b) : f j≠i := by intro hH; apply hi; rw [←hB,←hH]; exact mem_image_of_mem f hj
      refine ⟨hy,fun hF=>hg _ hF hy,hg,mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hx (mem_powerset.mp hu)),⟨?_,?_⟩⟩⟩
      · intro u h₁ v h₂ hE
        rcases mem_insert.mp h₁ with ha|ha <;> rcases mem_insert.mp h₂ with hb|hb
        · exact ha.trans hb.symm
        · exact False.elim (hg _ hb (hE.symm.trans ((congr_arg _ ha).trans hy)))
        · exact False.elim (hg _ ha (hE.trans ((congr_arg _ hb).trans hy)))
        exact hT ha hb hE
      rw [image_insert,hB]; rw [show f _= i from hy]
    rw [← Finset.sum_product']
    refine sum_bij (fun (x : α × Finset α) _=> insert x.1 x.2) (fun x hx=> (he x hx).2.2.2) ?_ ?_ (fun i hi=> ?_)
    · rintro ⟨x,a⟩ h₁ ⟨y,b⟩ h₂ hh
      obtain ⟨h,hu,hp,hq⟩:= he _ h₁; obtain ⟨j,hj,hs,hL⟩:= he _ h₂
      have hx : x∈ insert y b := hh ▸ mem_insert_self ..
      rcases mem_insert.mp hx with hx|hx
      · subst y; simp only at hh; exact congr_arg _ ((show a=b by
          ext k; by_cases hw:k=x
          · subst k; exact iff_of_false hu hj
          simpa only [Finset.mem_insert,hw,false_or] using! iff_of_eq (congr_arg (fun P:Finset α=> k∈P) hh)))
      exact False.elim (hs x hx h)
    · intro x hx; obtain ⟨hx,h₁,h₂⟩:=mem_filter.mp (show x∈Y from hx)
      obtain ⟨a,ha,hg⟩:=mem_image.mp (show i∈image f x from h₂.symm ▸ mem_insert_self ..)
      refine ⟨(a,x.erase a),mem_product.mpr ⟨mem_filter.mpr ⟨mem_powerset.mp hx ha,hg⟩,mem_filter.mpr ⟨mem_powerset.mpr (le_trans (erase_subset ..) (mem_powerset.mp hx)),h₁.mono (fun y hy=> mem_of_mem_erase hy),?_⟩⟩,insert_erase ha⟩
      ext b; constructor
      · intro hb; obtain ⟨m,hm,rfl⟩:= mem_image.mp hb; obtain ⟨ht,hp⟩:= mem_erase.mp hm
        exact (mem_insert.mp (show f m ∈ insert i s from h₂ ▸ mem_image_of_mem _ hp)).resolve_left (fun he=> ht (h₁ hp ha (he.trans hg.symm)))
      intro hb; obtain ⟨m,hm,hd⟩:=mem_image.mp (show b ∈ image f x from h₂.symm ▸ mem_insert_of_mem hb)
      exact mem_image.mpr ⟨m,mem_erase.mpr ⟨fun hh' => hi (by rw [← hg,← hh',hd];exact hb),hm⟩,hd⟩
    rw [prod_insert (he _ hi).2.1]

def peeled (C : α→Crate X) (P : α→ R) (x : Finset X) (i : Finset α) : R:= if ripe C i x then ∏ j∈i,P j else 0
lemma some (C : α→Crate X) (P : α→R) (x : Finset X) (Q : Finset α) :
    ∑ i∈Q.powerset,peeled C P x i=∑ s : Finset (Crate X),peeled id (fun i => ∑ j∈ Q.filter (fun j=> C j=i),P j) x s := by
  rw [← sum_fiberwise_of_maps_to (g:=fun s : Finset α=> s.image C) (s:=Q.powerset) (t:=univ) (fun _ _=>mem_univ _) (fun i=>peeled C P x i)]
  refine sum_congr rfl fun i _=> ?_
  unfold peeled; split_ifs with h
  · dsimp only; rw [one C P,sum_filter]; simp_rw [sum_filter]; apply sum_congr rfl; intro a _
    by_cases he : ripe C a x
    · rw [if_pos he]; have hf: ∀ i,fibres C a i ↔ image C a=i := fun i=>⟨fun h=> h.2,fun H=>⟨((picks C _ _).mp he).1.1,H⟩⟩; simp only [hf]
    have hx : ¬ fibres C a i:= fun H => he ((picks C a x).mpr ⟨by rw [H.2]; exact H,by rw [H.2];exact h⟩)
    rw [if_neg he,if_neg hx]; split <;> rfl
  refine sum_eq_zero fun i hi=> if_neg (fun H=> h ?_)
  rw [← (mem_filter.mp hi).2]; exact ((picks ..).mp H).2
end

section
variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [T2Space R] [ContinuousMul R] [ContinuousAdd R]

def piece (C : α→Crate X) (P : α→R) (i : Crate X) := ∑' j, if C j=i then P j else 0
lemma all (C : α→Crate X) (P : α→R) (x : Finset X) (h : Summable (peeled C P x))
    (hv : ∀ i,Summable fun j=> if C j=i then P j else 0) :
    ∑' i,peeled C P x i = ∑ i : Finset (Crate X),peeled id (piece C P) x i := by
  let Q := fun (i : Finset α) (j : Crate X) => ∑ a∈i.filter (fun a=>C a=j),P a
  let A:=fun i : Finset α=> ∑ x' : Finset (Crate X), peeled id (Q i) x x'
  have hp : Tendsto (fun p : Finset α=> p.powerset) atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro i; refine ⟨i.biUnion id, fun j hj u hu => mem_powerset.mpr fun a ha=> hj (mem_biUnion.mpr ⟨_,hu,show a∈id u from ha⟩)⟩
  have hf : Tendsto A atTop (𝓝 (∑' i,peeled C P x i)) := (show Tendsto (fun t : Finset (Finset α)=> ∑ i∈t,peeled C P x i) _ _ from h.hasSum).comp hp |>.congr fun i=> some C P x i
  refine tendsto_nhds_unique hf (tendsto_finsetSum _ fun j _=> ?_)
  simp only [peeled]; split
  · apply tendsto_finsetProd _ fun b _=> ?_
    unfold Q; simp_rw [sum_filter]; exact (hv b).hasSum
  exact tendsto_const_nhds
end
end YM.Next.Rank.Baler
