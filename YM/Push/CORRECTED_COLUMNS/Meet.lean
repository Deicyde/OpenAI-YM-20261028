import YM.Ac.Tree
import YM.Org.Theatre
import YM.Push.CORRECTED_COLUMNS.Rendezvous
/-!
# Reserve/cost for attaching the failed factors

Count them even if overlap multiple K. Build weighted field so that a
site-hit still pays the radius of *each* merged piece. This is independent
of which final marker coefficient is picked. All absolute budgets on the
inflated support; no counting just a syntactic fl-cut independent of
payload. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.UnionK
open Function Set Filter MeasureTheory Lattice Corona RG Wilson Marker Relation
open Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {V A : Type*} [DecidableEq V] [DecidableEq A] [Fintype A] {R : Census V}
variable {P : Rep G n} {v : V → Site n} (L : Original P v R) (Q : AddedHeads P v R A)

def touch (i : ℕ) := Finset.univ.filter fun j => ¬Disjoint (oldSites P i) (Q.support j)
def inflate (i : ℕ) := oldSites P i ∪ (touch Q i).biUnion Q.support
omit [DecidableEq A] in
lemma touch_test (i j) : j∈ touch Q i ↔ ¬Disjoint (oldSites P i) (Q.support j) := by unfold touch; simp

namespace Piece
variable {Q} (p : Piece Q)

-- map each index in component to old piece covering it in inflated graph
private lemma choose (t : ℕ ⊕ A) (h : t∈p.val) : ∃ s∈p.val.toLeft, patch Q t ⊆ inflate Q s ∧
    (∀ i : ℕ, t=Sum.inl i → i=s) ∧ (∀ i : A, t=Sum.inr i → i∈touch Q s) := by
  cases t with
  | inl i => exact ⟨i,mem_toLeft.mpr h, subset_union_left,fun j he => (Sum.inl.inj he).symm,fun _ e => by cases e⟩
  | inr a =>
    obtain ⟨k,hk⟩ := p.property.2.1
    have ht : ∀ j, Ac.chain (patch Q) p.val j (Sum.inr a) → j ≠ Sum.inr a →
        ∃ i∈ p.val.toLeft,a∈touch Q i := by
      intro j hj hue
      generalize hx : Sum.inr (α:=ℕ) a=y at hj
      induction hj with
      | refl => exact (hue hx.symm).elim
      | @tail q w _ hh ih =>
        subst w; by_cases e : q=Sum.inr a
        · exact ih e.symm
        obtain ⟨ha,hb,x,h1,h2⟩ := hh
        cases q with
        | inl q => exact ⟨q,mem_toLeft.mpr ha,(touch_test Q q a).mpr fun h => Finset.disjoint_left.mp h h1 h2⟩
        | inr b => exact (Finset.disjoint_left.mp (Q.distinct b a (fun H=>e (congr_arg _ H))) h1 h2).elim
    obtain ⟨i,hi,hv⟩ := ht (Sum.inl k) (p.property.1.2 _ (mem_toLeft.mp hk) _ h) (fun e => by cases e)
    refine ⟨i,hi, fun x hx => mem_union_right _ (mem_biUnion.mpr ⟨a,hv,hx⟩),(fun _ e => by cases e),?_⟩
    exact fun _ e => Sum.inr.inj e ▸ hv

lemma covers : unionOf Q p.val ⊆ p.val.toLeft.biUnion (inflate Q) := by
  intro x hx; obtain ⟨a,h1,h2⟩ := mem_biUnion.mp hx; obtain ⟨s,hs,h,ht⟩ := p.choose a h1
  exact mem_biUnion.mpr ⟨s,hs,h h2⟩
lemma blown : Ac.Spark (inflate Q) p.val.toLeft := by
  refine ⟨p.property.2.1, fun i hi j hj => ?_⟩
  have hp := p.property.1.2 (Sum.inl i) (mem_toLeft.mp hi) (Sum.inl j) (mem_toLeft.mp hj)
  choose! f hf hh using fun i (hi : i∈p.val) => p.choose i hi
  have he := hp.lift f (p:=Ac.bonds (inflate Q) p.val.toLeft) (fun x y h => by
    obtain ⟨a,b,z,hx,hy⟩ := h
    exact ⟨hf x a,hf y b,z,(hh x a).1 hx,(hh y b).1 hy⟩)
  change Ac.chain (inflate Q) p.val.toLeft (f (Sum.inl i)) (f (Sum.inl j)) at he
  rw [← (hh (Sum.inl i) (mem_toLeft.mp hi)).2.1 i rfl,← (hh (Sum.inl j) (mem_toLeft.mp hj)).2.1 j rfl] at he
  exact he
lemma stack : p.val.toRight ⊆ p.val.toLeft.biUnion (touch Q) := by
  intro i hi; obtain ⟨k,hk,-,-,h⟩ := p.choose (.inr i) (mem_toRight.mp hi)
  exact mem_biUnion.mpr ⟨k,hk,h _ rfl⟩
end Piece

variable {Q} (Y : ℕ ⊕ A → Poly R) (w : V → ℝ) (M : ℕ) (a γ : ℝ)
def faceBill (Q : AddedHeads P v R A) i := Poly.price w (Y (Sum.inl i)) * ∏ j∈touch Q i, (1+Poly.price w (Y (Sum.inr j)))
def limit (p : Piece Q) := ∏ i∈p.val,Y i
omit [DecidableEq A] [Fintype A] in
lemma dominated (h : ∀ i U, Width.Covered (value L Q i U) (Y i)) (p : Piece Q) (U) :
    Width.Covered (activated L p U) (limit Y p) := by
  have hp := Width.bulk p.val (F:=fun i => value L Q i U) (fun i _ => h i U)
  unfold activated; split; exact hp; exact hp.zero

-- integral sites: charge extra per K first
private lemma pile {ι W : Type*} [DecidableEq W] (I : Finset ι) (p : ι → Finset W) (v : W → ℝ) (hv : ∀ i, 1≤ v i) :
    ∏ x∈I.biUnion p,v x ≤ ∏ i∈I,∏ x∈p i,v x := by
  classical
  have hh (a b : Finset W) : ∏ i∈a∪b, v i ≤ (∏ i∈a,v i)*∏ i∈b,v i := by
    rw [← Finset.union_sdiff_of_subset (show b⊆a∪b from Finset.subset_union_right),Finset.prod_union]
    · rw [Finset.union_sdiff_right,mul_comm]; gcongr 1
      · exact Finset.prod_nonneg (fun i _ => zero_le_one.trans (hv i))
      refine prod_le_prod_of_subset_of_one_le (sdiff_subset ..) (fun i _ => zero_le_one.trans (hv i)) (fun i _ _ => hv i)
    exact Finset.disjoint_sdiff
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    rw [Finset.biUnion_insert,prod_insert hi]; exact (hh _ _).trans
      (mul_le_mul_of_nonneg_left ih (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hv i))))

variable {w a M γ}
lemma fiscal (hw : ∀ i, 0<w i) (ha : 0 ≤ a)
    (he : Ac.Hit (inflate Q) M (faceBill Y w Q) (a+1) γ) (hg : 0 ≤ γ)
    (h : (M+M+1:ℕ)^4*(γ:ℝ)≤1) :
    Ac.Hit (fun p : Piece Q => unionOf Q p.val) M (fun p => Poly.price w (limit Y p)) a (Real.exp γ-1) := by
  classical
  let f i := Poly.price w (Y (Sum.inl i)); let t i := Poly.price w (Y (Sum.inr i))
  have hf i : 0 ≤ f i := Poly.nonnegative hw _
  have ht i : 0 ≤ t i := Poly.nonnegative hw _
  have hT i : 1 ≤ 1+t i := le_add_of_nonneg_right (ht i)
  have hK i : 0 ≤ faceBill Y w Q i := mul_nonneg (hf i)
    (prod_nonneg fun j _ => zero_le_one.trans (hT j))
  intro x
  let T (p : Piece Q) := if x∈unionOf Q p.val then Poly.price w (limit Y p) * Real.exp (a*coverNumber M (unionOf Q p.val)) else 0
  have hu p : 0 ≤ T p := by unfold T; split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl
  have hy := Ac.forest (inflate Q) M ha hK he h hg x
  let U := Ac.roots (inflate Q) M (faceBill Y w Q) a x
  have HH (s : Finset (Piece Q)) (l : Finset ℕ) (H : ∀ i∈s,x∈unionOf Q i.val ∧ i.val.toLeft=l) :
      ∑ i∈s,T i≤U l := by
    rcases s.eq_empty_or_nonempty with HE|HE
    · rw [HE,Finset.sum_empty]; exact hy.1 _
    obtain ⟨z,hz⟩ := HE
    let X := l.biUnion (inflate Q)
    have hv i (hi : i∈s) : unionOf Q i.val ⊆ X := (show unionOf Q i.val ⊆ l.biUnion _ from (H i hi).2 ▸ Piece.covers i)
    let p := ∏ i∈l,f i
    let c := Real.exp (a*coverNumber M X)
    let r i := ∏ j∈i,t j
    have Hd i (hi : i∈s) : T i ≤ c*p*r i.val.toRight := by
      unfold T; rw [if_pos (H i hi).1,mul_comm]
      have hs : Poly.price w (limit Y i) ≤ p*r i.val.toRight := by
        apply le_trans (Poly.multiple hw i.val _) (le_of_eq ?_)
        rw [prod_sum_eq_prod_toLeft_mul_prod_toRight,(H i hi).2]
      rw [mul_assoc]
      refine mul_le_mul ?_ hs (Poly.nonnegative hw _) (Real.exp_pos _).le
      exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast cover_mono (hv i hi) M) ha)
    let W := l.biUnion (touch Q)
    let J (i : Piece Q) := i.val.toRight
    have hJ : s.image J ⊆ W.powerset := by
      intro j hj; obtain ⟨i,hi,hj⟩ := mem_image.mp hj; subst j
      apply mem_powerset.mpr
      exact show i.val.toRight ⊆ l.biUnion (touch Q) from (H i hi).2 ▸ Piece.stack i
    have hi : InjOn J s := by
      intro i hi j hj hp; apply Subtype.ext
      calc i.val=i.val.toLeft.disjSum i.val.toRight := Finset.toLeft_disjSum_toRight.symm
           _ = _ := (congr_arg₂ Finset.disjSum ((H i hi).2.trans (H j hj).2.symm) hp).trans Finset.toLeft_disjSum_toRight
    have hA : Ac.Spark (inflate Q) l := (H z hz).2 ▸ Piece.blown z
    have hB : x∈ X := hv z hz (H z hz).1
    have hC : U l=c*p* (∏ i∈l,∏ j∈touch Q i,(1+t j)) := by
      unfold U Ac.roots; rw [if_pos ⟨hA,hB⟩]
      simp only [faceBill,Finset.prod_mul_distrib]
      rw [mul_assoc]
    calc
      _ ≤ ∑ i∈s,c*p*r (J i) := sum_le_sum Hd
      _ = c*p*∑ i∈s.image J,r i := by rw [sum_image hi, mul_sum]
      _ ≤ _ := by
        rw [hC]; refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.exp_pos _).le (prod_nonneg fun i _ => hf i))
        refine (sum_le_sum_of_subset_of_nonneg hJ (fun i _ _ => prod_nonneg fun j _ => ht j)).trans ?_
        rw [← prod_one_add]; exact pile _ _ _ hT
  let k (p : Piece Q) := p.val.toLeft
  have htau (s : Finset (Piece Q)) : ∑ i∈s,T i≤Real.exp γ-1 := by
    let t := s.filter fun i => x∈unionOf Q i.val
    have he : s.filter (fun i => x∈unionOf Q i.val)=t := rfl
    have hv : ∑ i∈s,T i=∑ i∈t,T i := by
      symm; refine sum_subset (filter_subset _ s) fun i hi hu => ?_; unfold T; split; rename_i ht; exact False.elim (hu (mem_filter.mpr ⟨hi,ht⟩)); rfl
    rw [hv,← Finset.sum_fiberwise_of_maps_to (f:=T) (show ∀ i∈t,k i∈t.image k from fun i hi => mem_image_of_mem k hi)]
    exact (sum_le_sum (fun i _ => HH _ i (fun p hp =>
      ⟨(mem_filter.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩))).trans ((hy.2.1.sum_le_tsum _ (fun _ _ => hy.1 _)).trans hy.2.2)
  have ht := summable_of_sum_le (f:=T) hu htau
  exact ⟨hu,ht,ht.tsum_le_of_sum_le htau⟩
end YM.Push.Corrected.UnionK
