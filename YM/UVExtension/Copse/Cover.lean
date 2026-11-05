import YM.Ac.Tree
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.ABSOLUTE_SUMS.Footprint

/-!
 # Multicover root
 Up to finitely many disconnected B-clumps. We will use this only for
 polynomial growth estimates. No use to bound a winding log reset
 from affine tests! "Partners" always use the usual connected-cover
 price, and charge at *actual* site overlaps.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Copse
open Function Filter Lattice Lattice.Corona Wilson RG Finset Relation Set Push Push.AbsoluteSums Footprint Ac Animals
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι:Type*}{n:Side}
variable (d B:ℕ)
private def Paid (p:Support n)(k:ℕ):Prop := ∃ X:Fin (d+1)→ Support n,p⊆ Finset.univ.biUnion X ∧ k= ∑ i,coverNumber B (X i)
private def solo (p:Support n)(i:Fin (d+1)):= if i=0 then p else ∅
private lemma awarded (p:Support n): Paid d B p (coverNumber B p) := by
  refine ⟨solo d p,fun i hi=> mem_biUnion.mpr ⟨0,mem_univ _,by simpa only [solo,↓reduceIte]⟩,?_⟩
  rw [Finset.sum_eq_single 0]; · simp [solo]
  · intro j _ h; simp [solo,h,Animals.price_zero]
  simp
private lemma pays (p:Support n):∃ k,Paid d B p k:=⟨_,awarded d B p⟩

def cover (p:Support n) := Nat.find (pays d B p)
lemma funded (p:Support n): ∃ X:Fin (d+1)→Support n,p ⊆ Finset.univ.biUnion X∧ cover d B p=∑ i, coverNumber B (X i):= Nat.find_spec (pays d B p)
lemma cheaper (p:Support n) (X:Fin (d+1)→Support n)(he:p⊆Finset.univ.biUnion X):cover d B p ≤ ∑ i,coverNumber B (X i):= Nat.find_min' _ (show Paid d B p _ from ⟨X,he,rfl⟩)
lemma oldCost (p:Support n): cover d B p ≤ coverNumber B p:= Nat.find_min' _ (awarded d B p)
lemma empty : cover d B (∅:Support n)=0:= Nat.eq_zero_of_le_zero ((oldCost d B ∅).trans_eq (Animals.price_zero B))
lemma one (p:Support n): cover 0 B p=coverNumber B p:=by
   refine le_antisymm (oldCost ..) ?_
   obtain ⟨X,h,hQ⟩:=funded 0 B p; rw [hQ]; change coverNumber B p ≤ ∑ i:Fin 1,coverNumber B (X i); rw [Fin.sum_univ_one]; exact cover_mono (show p⊆X 0 from fun i hi=> by obtain ⟨j,h',hi⟩:=mem_biUnion.mp (h hi); rwa [show j=0 from (Subsingleton.elim (α:=Fin 1) _ _)] at hi) _ -- ambiguous cover_mono
lemma size (p:Support n): p.card ≤ cover d B p*ballCost B:=by
    obtain ⟨X,h,hv⟩:= funded d B p; refine (Finset.card_le_card h).trans ((Finset.card_biUnion_le ..).trans ?_); rw [hv,sum_mul]; exact Finset.sum_le_sum fun i _=> Corona.pays (X i) B
lemma mono {s t:Support n}(h : s ⊆ t): cover d B s ≤ cover d B t := by
   obtain ⟨X,hT,hQ⟩:=funded d B t; rw [hQ]; exact cheaper d B s X (Finset.Subset.trans h hT)
-- connected overlap when partner uses ordinary coverNumber
lemma linked {s t:Support n} {x} (hs:x∈s) (ht:x∈t) : cover d B (t∪s) ≤ coverNumber B t + cover d B s:=by
    obtain ⟨X,h,hv⟩:=funded d B s; obtain ⟨i,-,hi⟩:= mem_biUnion.mp (h hs); let Y(b):= if b=i then t∪X i else X b
    have he j:X j⊆ Y j:=by
      unfold Y; split; next h=> rw [h]; exact Finset.subset_union_right
      exact Finset.Subset.refl _
    apply le_trans (cheaper d B _ Y ?_); swap
    · intro l hl; rcases Finset.mem_union.mp hl with hj|hj
      · exact mem_biUnion.mpr ⟨i,mem_univ _,by rw [show Y i=t∪X i from if_pos rfl]; exact mem_union_left _ hj⟩
      obtain ⟨j,-,hj⟩:=mem_biUnion.mp (h hj); exact mem_biUnion.mpr ⟨j,mem_univ _,he j hj⟩
    rw [hv,← Finset.add_sum_erase _ _ (mem_univ i),← Finset.add_sum_erase _ (fun j=>coverNumber B (X j)) (mem_univ i),show Y i=t∪X i from if_pos rfl, ← add_assoc]; apply Nat.add_le_add (Corona.meets_sum ht hi B) (le_of_eq (Finset.sum_congr rfl fun j hj=> congr_arg (coverNumber B) (if_neg (ne_of_mem_erase hj))))

-- force root support in induction from the beginning. Distinct vertices (even if labels equal weights).
lemma priced [DecidableEq ι] (X:ι→ Support n) {s:Finset ι} {j:ι} (he:Ac.Spark X s) (h:j∈s) :
    cover d B (s.biUnion X) ≤ cover d B (X j)+∑ i∈s.erase j,coverNumber B (X i) := by
  have ht:∀ k:ℕ,k+1 ≤ s.card → ∃ u⊆s,j∈u ∧ u.card=k+1 ∧ cover d B (u.biUnion X)≤cover d B (X j)+ ∑ i∈u.erase j,coverNumber B (X i):=by
    intro k; induction k with
    | zero=> exact fun _ => ⟨{j},by simp [h],by simp,by simp,by simp⟩
    | succ k IH=>
       intro hk; obtain ⟨v,hv,hj,hV,hp⟩:= IH (by omega)
       obtain ⟨i,hI,hi⟩:= exists_mem_notMem_of_card_lt_card (show v.card < s.card by omega)
       have H :∀ i,chain X s j i → i∉v→∃ l∈s,l∉ v ∧ meets X l (v.biUnion X):= by
          intro i he; induction he with
          | refl => exact fun hh => absurd hj hh
          | @tail a b _ hh I=>
             intro hi; by_cases hx:a∈v; swap; · exact I hx
             obtain ⟨x,hA,hB⟩:=hh.2.2; exact ⟨_,hh.2.1,hi,_,mem_biUnion.mpr ⟨_,hx,hA⟩,hB⟩
       obtain ⟨l,hl,hx,x,hP,hL⟩:= H _ (he.2 _ h _ hI) hi
       have hn : l≠j:=fun hh=>hx (hh.symm ▸ hj)
       refine ⟨insert l v,Finset.insert_subset hl hv,mem_insert_of_mem hj,by simp [hx,hV],?_⟩
       rw [Finset.biUnion_insert,Finset.erase_insert_of_ne hn,Finset.sum_insert (fun h=> hx (mem_of_mem_erase h))]; exact (linked d B hP hL).trans ((Nat.add_le_add_left hp _).trans_eq (add_left_comm ..))
  obtain ⟨v,hv,hj,hV,hp⟩:= ht (s.card-1) (by have hp:=Finset.card_pos.mpr he.1; omega)
  have hQ:v=s:=Finset.eq_of_subset_of_card_le hv (by omega); rwa [hQ] at hp
attribute [local instance] Classical.propDecidable
lemma mutate {f:Side} (r:Ratio n f)(M l:ℕ) (hx:Support f)(ht:0 < B)(hB:M ≤ 2*B) : (cover d B (enlargement r l B (inspected hx)):ℝ) ≤ (d+1)*preCost (l+5)+conversion r (l+5)*cover d M hx := by
  obtain ⟨X,h,hK⟩:= funded d M hx; let v:= l+5; let Y(i):=enlargement r v B (X i); refine Nat.cast_le.mpr (cheaper d B _ Y ?_) |>.trans ?_
  · intro i hi; obtain ⟨j,hj,hp⟩:= halo_spec.mp (inspected_price r l B hx ht hi); obtain ⟨q,hq,rfl⟩:= mem_image.mp hj; obtain ⟨a,ha,hv⟩:= mem_biUnion.mp (h hq); exact mem_biUnion.mpr ⟨a,ha,halo_spec.mpr ⟨_,mem_image_of_mem _ hv,hp⟩⟩
  push_cast
  apply le_trans (Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset (Fin (d+1))))=>footprint r v B M (X i) ht hB)); rw [hK, Nat.cast_sum, Finset.sum_add_distrib,Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum]; push_cast; rfl
end YM.UVExtension.Copse
