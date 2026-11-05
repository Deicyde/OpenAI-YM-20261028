import YM.Next.RANK.Alarm

/-! Exact correspondence of selected components at two flags and all optional labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {ι κ : Type}
variable {ζ : V→Site n} {τ t : ℝ}
variable (A : ι→ Lifted G ζ t) (B : κ→ Strike G ζ τ) (X : Siren G n τ)
lemma initials (i) : (vol A B X i).Nonempty := by
  cases i with
  | inl i=>
    rcases i with i|i
    · exact ((A i).needed.mono (A i).records).mono (vol_unit A B X _)
    exact (B i).active
  | inr i=>exact ⟨_,X.marked i⟩

variable [DecidableEq ι] [DecidableEq κ]

def unpeel (p : Finset (Domino A B X)) := p.biUnion Subtype.val

def n_good (p : Finset (Domino A B X)) (U) := Lifted.gather (teat A B X) p U ∧ ∀ i∈p, inside A B X i U

omit [DecidableEq ι] [DecidableEq κ] in
private lemma unwindable (p : Finset (Domino A B X)) (h : (p : Set _).PairwiseDisjoint (Settle A B X)) :
    (p:Set (Domino A B X)).PairwiseDisjoint Subtype.val := by
  intro i hi j hj hn; apply disjoint_left.mpr
  intro x hx he; obtain ⟨z,hz⟩:=initials A B X x
  exact disjoint_left.mp (h hi hj hn) (mem_biUnion.mpr ⟨x,hx,hz⟩) (mem_biUnion.mpr ⟨x,he,hz⟩)

private lemma unwind (p : Finset (Domino A B X)) (h : (p:Set _).PairwiseDisjoint (Settle A B X)) :
    Ac.Parts (vol A B X) (unpeel A B X p) = p.image Subtype.val := by
  rw [show unpeel A B X p=(p.image Subtype.val).biUnion id by ext;simp [unpeel]]; apply Ac.separates
  · intro j hj; obtain ⟨j,hj,rfl⟩:=mem_image.mp hj; exact j.property.1
  intro i hi j hj hn; obtain ⟨a,ha,rfl⟩:=mem_image.mp hi; obtain ⟨b,hb,rfl⟩:=mem_image.mp hj
  exact h ha hb fun H=> hn (congr_arg Subtype.val H)

private lemma peel_preserves (p : Finset (Domino A B X)) (U) (h : n_good A B X p U) :
    Lifted.pack (teat A B X) p U=quake A B X (unpeel A B X p) U := by
  rw [Lifted.pack, if_pos h.1, quake,unpeel,prod_biUnion (unwindable A B X p h.1.1)]; apply prod_congr rfl; intro j hj; rw [teat_pay,if_pos (h.2 _ hj)]; rfl

omit [DecidableEq ι] [DecidableEq κ] in
private lemma peel_void (p : Finset (Domino A B X)) (U) (h : ¬ n_good A B X p U) : Lifted.pack (teat A B X) p U=0 := by
  rw [Lifted.pack]; split_ifs with hi
  · have hp : ∃ j∈p, ¬ inside A B X j U := Classical.byContradiction fun he => h ⟨hi, not_exists_not.mp fun ⟨j,hq⟩=> by push Not at hq; exact he ⟨j,hq.1,hq.2⟩⟩
    obtain ⟨j,hj,hg⟩:= hp; apply prod_eq_zero hj; rw [teat_pay,if_neg hg]
  rfl

def lawful (p : Finset (Branch ι κ n)) U := Lifted.gather A p.toLeft.toLeft U ∧ p.toRight=flags τ U

lemma rolled (p U) (h : n_good A B X p U) (hu : τ ≤ t) : lawful (τ:=τ) A (unpeel A B X p) U := by
  let P:= unpeel A B X p; let R:=Settle A B X
  have ht : (p:Set _).PairwiseDisjoint R:= h.1.1
  have hg : P.toRight = flags τ U := by
    apply Eq.trans _ h.1.2; ext i; simp only [P,unpeel,mem_toRight,mem_biUnion]; refine exists_congr fun j=> ?_; exact and_congr_right fun hj=> mem_toRight.symm
  refine ⟨⟨fun i hi j hj hp=>?_,?_⟩, hg⟩
  · obtain ⟨a,ha,hL⟩:=mem_biUnion.mp (mem_toLeft.mp (mem_toLeft.mp hi)); obtain ⟨b,hb,hb'⟩:=mem_biUnion.mp (mem_toLeft.mp (mem_toLeft.mp hj))
    rcases eq_or_ne a b with hba|he
    · subst b; exact a.property.2.2 (mem_toLeft.mpr (mem_toLeft.mpr hL)) (mem_toLeft.mpr (mem_toLeft.mpr hb')) hp
    exact disjoint_left.mpr fun x hx hv => disjoint_left.mp (ht ha hb he) (mem_biUnion.mpr ⟨.inl (.inl i),hL,vol_unit A B X i hx⟩) (mem_biUnion.mpr ⟨.inl (.inl j),hb',vol_unit A B X j hv⟩)
  ext x; constructor
  · intro hx; obtain ⟨i,hi,hU⟩:=mem_biUnion.mp hx; obtain ⟨a,ha,hV⟩:=mem_biUnion.mp (mem_toLeft.mp (mem_toLeft.mp hi)); refine (mem_inter.mp (show x ∈ a.val.toRight∩flags t U from ?_)).2
    rw [(h.2 a ha).2]; exact mem_biUnion.mpr ⟨i,mem_toLeft.mpr (mem_toLeft.mpr hV),hU⟩
  intro hv; obtain ⟨a,ha,H⟩:=mem_biUnion.mp (mem_toRight.mp (hg.symm ▸ threshold τ t hu U hv))
  obtain ⟨j,hj,he⟩:=mem_biUnion.mp (show x ∈ _ from ((h.2 a ha).2 ▸ mem_inter.mpr ⟨mem_toRight.mpr H,hv⟩))
  exact mem_biUnion.mpr ⟨j,mem_toLeft.mpr (mem_toLeft.mpr (mem_biUnion.mpr ⟨a,ha,mem_toLeft.mp (mem_toLeft.mp hj)⟩)),he⟩

private lemma receives (p : Finset (Branch ι κ n)) (U) (hp : lawful (τ:=τ) A p U) (he : quake A B X p U≠0)
    (ht : τ ≤ t) : ∃ a : Finset (Domino A B X), n_good A B X a U ∧ unpeel A B X a=p := by
  let Z:=vol A B X; let S:=Ac.Parts Z p
  have hy a (ha:a∈p) : fuel A B X a U≠0 := fun hv=>he (prod_eq_zero ha hv)
  have hq (q) (h:q∈S) (x y : Branch ι κ n) (hx : x∈q) (hy : y∈p) (ht : ¬Disjoint (Z x) (Z y)) : y∈q := by
    rw [← Ac.contains Z h _ hx]; apply (Ac.bright ..).mpr
    obtain ⟨a,ha,hb⟩:= Finset.not_disjoint_iff.mp ht; exact ⟨hy, .single ⟨(Ac.lives _ _ h).1 hx,hy,a,ha,hb⟩⟩
  have hh g (hi : g∈ S) : cast A B X g := by
    obtain ⟨hj,hH⟩:= Ac.lives Z p hi; refine ⟨hH, ?_,fun i hi j hL=> hp.1.1 (toLeft_subset_toLeft (toLeft_subset_toLeft hj) hi) (toLeft_subset_toLeft (toLeft_subset_toLeft hj) hL)⟩
    obtain ⟨j,hj'⟩:=hH.1; rcases j with (j|j)|j
    · obtain ⟨x,hx⟩:= (A j).needed; have hx' : x ∈ flags t U := by rw [← hp.1.2]; exact mem_biUnion.mpr ⟨j,mem_toLeft.mpr (mem_toLeft.mpr (hj hj')),hx⟩
      have hx'' : x∈p.toRight := hp.2.symm ▸ threshold τ t ht _ hx'; refine ⟨x,mem_toRight.mpr ?_⟩; apply hq _ hi _ _ hj' (mem_toRight.mp hx'')
      exact Finset.not_disjoint_iff.mpr ⟨x,vol_unit A B X _ ((A j).records hx),X.marked x⟩
    · have ht : ¬ Healthy τ (B j).extent U:= fun hx=> hy _ (hj hj') ((congr_arg (Poly.send (B j).fires) ((B j).only U hx)).trans (Poly.send_zero _))
      obtain ⟨x,hs,hx⟩:= Finset.not_disjoint_iff.mp ht
      refine ⟨x,mem_toRight.mpr (hq _ hi _ _ hj' (mem_toRight.mp (hp.2.symm ▸ hx)) (Finset.not_disjoint_iff.mpr ⟨x,hs,X.marked x⟩))⟩
    exact ⟨j,mem_toRight.mpr hj'⟩
  let a:= S.preimage (Subtype.val (p:=cast A B X)) Subtype.val_injective.injOn
  have ha : a.image Subtype.val=S := by
    ext i; constructor
    · intro H; obtain ⟨x,hx,rfl⟩:=mem_image.mp H; exact mem_preimage.mp hx
    intro H; exact mem_image.mpr ⟨⟨_,hh i H⟩,mem_preimage.mpr H,rfl⟩
  have hf : unpeel A B X a=p:= by rw [show unpeel A B X a=(a.image Subtype.val).biUnion id by ext;simp [unpeel],ha]; exact Ac.reconstruct Z p
  refine ⟨a,⟨⟨fun i hi j hj hn=> ?_, ?_⟩,fun i hi=>?_⟩,hf⟩
  · apply Ac.separate Z p (mem_preimage.mp hi) (mem_preimage.mp hj); exact fun H=>hn (Subtype.ext H)
  · rw [←hp.2,←hf]; ext x; simp [unpeel,teat]
  have heq : i.val ∈ S:= mem_preimage.mp hi; have h:= (Ac.lives Z p heq).1
  refine ⟨?_,?_⟩ <;> ext x <;> rw [mem_inter] <;> constructor
  · rintro ⟨hg,hb⟩; obtain ⟨z,hz,hd⟩:= mem_biUnion.mp hg
    exact mem_toRight.mpr (hq _ heq z _ hz (mem_toRight.mp (hp.2.symm ▸ hb)) (Finset.not_disjoint_iff.mpr ⟨x,hd,X.marked _⟩))
  · intro hg; exact ⟨(teat A B X i).records hg,hp.2 ▸ toRight_subset_toRight h hg⟩
  · rintro ⟨ht,hx⟩; obtain ⟨v,hv,hL⟩:= mem_biUnion.mp (hp.1.2.symm ▸ hx); apply mem_biUnion.mpr; refine ⟨v,?_,hL⟩
    exact mem_toLeft.mpr (mem_toLeft.mpr (hq _ heq _ _ (mem_toRight.mp ht) (mem_toLeft.mp (mem_toLeft.mp hv)) (Finset.not_disjoint_iff.mpr ⟨x,X.marked _,vol_unit A B X _ ((A v).records hL)⟩)))
  intro hz; obtain ⟨b,hb,hs'⟩:= mem_biUnion.mp hz
  have hp' : x∈flags t U := hp.1.2 ▸ mem_biUnion.mpr ⟨b,toLeft_subset_toLeft (toLeft_subset_toLeft h) hb,hs'⟩
  exact ⟨mem_toRight.mpr (hq _ heq _ _ (mem_toLeft.mp (mem_toLeft.mp hb)) (mem_toRight.mp (hp.2.symm ▸ threshold τ t ht U hp'))
      (Finset.not_disjoint_iff.mpr ⟨x,vol_unit A B X _ ((A b).records hs'),X.marked _⟩)),hp'⟩

variable [Fintype ι] [Fintype κ]

lemma charade (U) (H : τ ≤ t) :
    (∑ i : Finset ι,Lifted.pack A i U)*(∏ j:κ,((B j).occ U + 1))*
          (∏ i∈flags τ U,Nreal (X.value i U)) = ∑ s : Finset (Domino A B X), Lifted.pack (teat A B X) s U := by
  let Z:=univ.filter fun p : Finset (Domino A B X)=> n_good A B X p U
  let Y:=univ.filter fun p : Finset (Branch ι κ n)=> lawful (τ:=τ) A p U
  have hr : ∑ i∈Z,Lifted.pack (teat A B X) i U=∑ j∈Y,quake A B X j U := by
    let X':=Z.image (unpeel A B X)
    have hh : X'⊆Y := by intro i hi; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; exact mem_filter.mpr ⟨mem_univ _,rolled A B X i U (mem_filter.mp (show i∈Z from by aesop)).2 H⟩
    rw [← Finset.sum_subset hh, Finset.sum_image]
    · apply sum_congr rfl; intro i hi; exact peel_preserves A B X i U (mem_filter.mp hi).2
    · intro i hi j hj he; have ha:=unwind A B X i ((mem_filter.mp hi).2.1.1); rw [he,unwind A B X j ((mem_filter.mp hj).2.1.1)] at ha; exact image_inj Subtype.val_injective|>.mp ha.symm
    intro i hi hl; apply Classical.byContradiction; intro hq
    obtain ⟨j,hj,hk⟩:=receives A B X i U (mem_filter.mp hi).2 hq H; exact hl (mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩,hk⟩)
  rw [← Finset.sum_subset (subset_univ Z) (fun i hi hn=> peel_void A B X i U (fun h=> hn (mem_filter.mpr ⟨hi,h⟩))),hr,
    show (∏ j : κ,((B j).occ U + 1))=∑ i : Finset κ,∏ j∈i,(B j).occ U by simpa using Fintype.prod_add (fun i => (B i).occ U) (fun _=>1),Finset.sum_mul_sum,Finset.sum_mul]; simp_rw [Finset.sum_mul]
  let F:=univ.filter fun i:Finset ι=> Lifted.gather A i U; let b:= flags τ U; let c:=flags t U
  let v (j : Finset ι ×Finset κ) := (j.1.disjSum j.2).disjSum b
  have he (j : Finset ι ×Finset κ) (hj : j∈F×ˢuniv) : v j∈Y := by
    obtain ⟨hh,h⟩:=mem_product.mp hj; have hu:= (mem_filter.mp hh).2; refine mem_filter.mpr ⟨mem_univ _,?_⟩
    exact ⟨by unfold v; rw [toLeft_disjSum,toLeft_disjSum]; exact hu, toRight_disjSum ..⟩
  rw [← Finset.sum_subset (subset_univ F) ?_]
  · rw [← sum_product']
    refine Finset.sum_bij (fun i _=> v i) he ?_ ?_ ?_
    · rintro ⟨i,j⟩ hi ⟨a,d⟩ ha hh
      have ht := congr_arg (fun p : Finset (Branch ι κ n)=> (p.toLeft.toLeft,p.toLeft.toRight)) hh; simpa [v] using ht
    · intro i hi; obtain ⟨hg,hp⟩:= (mem_filter.mp hi).2
      refine ⟨(i.toLeft.toLeft,i.toLeft.toRight),mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hg⟩,mem_univ _⟩,?_⟩
      unfold v b; rw [← hp]; simp [toLeft_disjSum_toRight]
    rintro ⟨a,d⟩ ha; have hq := (mem_filter.mp (mem_product.mp ha).1).2
    rw [Lifted.pack,if_pos hq]; unfold quake v; simp only [Finset.prod_disjSum]; rfl
  intro i hi hn; have hv : Lifted.pack A i U=0 := if_neg (fun H=> hn (mem_filter.mpr ⟨hi,H⟩)); apply sum_eq_zero; simp_rw [hv,zero_mul]; simp
end YM.Next.Rank.Alarm
