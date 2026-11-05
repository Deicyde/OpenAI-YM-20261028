import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import YM.RG.History
import YM.SectorNext.VACUUM_NORMALIZATION.Deletion


/-!
# Deletion on actual countable disjoint-family sums

Support-hits sufficient, NOT assuming absolute summability of the desired
connected sum or nonvanishing. Nonempty *support* required on every
address, including a zero coefficient. At this point these labels will
be used for UNFORCED species **after** first gas assembly, not assumed
available before the Gaussian etc estimates. Native cover receipts and
actual forcing below.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SectorNext.Vacuum.ReLog
open Finset Function Filter RG
open scoped Topology BigOperators Classical
variable {J ι : Type*} [Fintype J] [DecidableEq J]

local notation "expo" => Real.exp

variable (X : ι → Leaf J)

def stays (B : Leaf J) (I Q : Finset ι) : Prop := Q ⊆ I ∧
  (∀ i∈Q,X i ⊆ B) ∧ (Q : Set ι).Pairwise fun i j => Disjoint (X i) (X j)
def accepted (B : Leaf J) (I : Finset ι) := I.powerset.filter (stays X B I)
lemma accepts (B : Leaf J) (I Q : Finset ι) : Q∈accepted X B I ↔ stays X B I Q := by simp [accepted,stays]

def stock (v : ι → ℝ) (I : Finset ι) (B : Leaf J) := ∑ Q∈accepted X B I,∏ i∈Q,v i

def crowd (v : ι → ℝ) (I : Finset ι) (P : Leaf J) := ∑ i∈I,if X i=P then v i else 0

private def spokes (I : Finset ι) (B : Leaf J) (x : J) := I.filter fun i => X i ⊆ B ∧ x∈X i

private lemma sorting (I : Finset ι) (B : Leaf J) (x : J) (v : ι → ℝ) (E : Grid J) :
    ∑ i∈spokes X I B x,v i*E (X i)=∑ P∈owners B x,crowd X v I P*E P := by
  unfold spokes
  rw [Finset.sum_filter (s:=I)] -- spokes def
  unfold crowd; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]; apply sum_congr rfl
  intro i hi; unfold owners; simp_rw [ite_mul,zero_mul]
  by_cases he : X i ⊆ B ∧ x∈X i <;> simp [he]

lemma extend_stays (B : Leaf J) (I : Finset ι) (i : ι) (h : i∈I) (he : X i ⊆ B) (Q : Finset ι) (hi : i∉Q) :
    insert i Q ∈ accepted X B I ↔ Q∈ accepted X (B\X i) I := by
  simp only [accepts, stays, insert_subset_iff, h, true_and, mem_insert, Finset.coe_insert]
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    refine ⟨h₁,fun j hj x hx => ?_,?_⟩
    · apply Finset.mem_sdiff.mpr; refine ⟨h₂ j (Or.inr hj) hx,?_⟩
      intro h; exact Finset.disjoint_left.mp (h₃ (Set.mem_insert_of_mem _ hj) (Set.mem_insert _ _) (ne_of_mem_of_not_mem hj hi)) hx h
    exact h₃.mono (Set.subset_insert i _)
  rintro ⟨h₁,h₂,h₃⟩
  refine ⟨h₁,fun j hj => hj.elim (fun e => e.symm ▸ he) (fun h => (h₂ j h).trans sdiff_subset),?_⟩
  intro a ha b hb hd
  have hh (j : ι) (hj : j∈Q) : Disjoint (X j) (X i) := Finset.disjoint_left.mpr fun k hk => (Finset.mem_sdiff.mp (h₂ j hj hk)).2
  obtain hr|hr := Set.mem_insert_iff.mp ha <;> obtain hy|hy := Set.mem_insert_iff.mp hb
  · exact False.elim (hd (hr.trans hy.symm))
  · subst a; exact (hh b hy).symm
  · subst b; exact hh a hr
  exact h₃ hr hy hd

/-- Deletion is exact on any finite truncation (no occupancy or cardinal
correction). The labels of equal support are still counted. -/
theorem stock_deletion (B : Leaf J) (I : Finset ι) (v : ι → ℝ) (hn : ∀ i,(X i).Nonempty) (x : J) (_ : x∈B) :
    stock X v I B = stock X v I (B.erase x)+∑ P∈owners B x,crowd X v I P*stock X v I (B\P) := by
  let F := accepted X B I
  let Y := spokes X I B x
  rw [← sorting X I B x v (fun P=>stock X v I (B\P))]
  let E (i) := (accepted X (B\X i) I).image (insert i)
  have h0 (i : ι) (Q) (hq : Q∈accepted X (B\X i) I) : i∉Q := by
    intro h
    obtain ⟨x,hx⟩ := hn i
    exact (Finset.mem_sdiff.mp (((accepts ..).mp hq).2.1 i h hx)).2 hx
  have he (i) (hi : i∈Y) : E i = F.filter (fun Q => i∈Q) := by
    obtain ⟨h₁,h₂,h₃⟩ := mem_filter.mp hi
    ext Q; constructor
    · intro h; obtain ⟨Q,hQ,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨(extend_stays X B I i h₁ h₂ Q (h0 i Q hQ)).mpr hQ,mem_insert_self ..⟩
    intro h; obtain ⟨ht,hI⟩ := mem_filter.mp h
    refine mem_image.mpr ⟨Q.erase i,(extend_stays X B I i h₁ h₂ _ (notMem_erase _ _)).mp ?_,insert_erase hI⟩
    rwa [insert_erase hI]
  let G := accepted X (B.erase x) I
  have hg (Q) : Q∈G ↔ Q∈F ∧ ∀ i∈Y,i∉Q := by
    constructor
    · intro h; obtain ⟨h₁,h₂,h₃⟩ := (accepts ..).mp h
      refine ⟨(accepts ..).mpr ⟨h₁,fun i he => (h₂ i he).trans (erase_subset ..),h₃⟩,fun i hi he => ?_⟩
      exact notMem_erase x B (h₂ i he (mem_filter.mp hi).2.2)
    rintro ⟨hh,hk⟩; obtain ⟨h₁,h₂,h₃⟩ := (accepts ..).mp hh
    exact (accepts ..).mpr ⟨h₁,fun i hi => subset_erase.mpr ⟨h₂ i hi,fun h => hk i (mem_filter.mpr ⟨h₁ hi,h₂ i hi,h⟩) hi⟩,h₃⟩
  have hh : (Y : Set ι).PairwiseDisjoint E := by
    intro i hi j hj h; apply Finset.disjoint_left.mpr; intro Q hQ ht
    rw [he i hi] at hQ; rw [he j hj] at ht
    obtain ⟨h₁,h₂⟩ := mem_filter.mp hQ
    exact Finset.disjoint_left.mp (((accepts ..).mp h₁).2.2 h₂ (mem_filter.mp ht).2 h) (mem_filter.mp (show i∈Y from hi)).2.2 (mem_filter.mp (show j∈Y from hj)).2.2
  have hk : Disjoint G (Y.biUnion E) := Finset.disjoint_left.mpr fun Q hQ ht => by
    obtain ⟨i,hi,hI⟩ := mem_biUnion.mp ht; rw [he i hi] at hI; exact (hg Q |>.mp hQ).2 i hi (mem_filter.mp hI).2
  have hp : F=G∪Y.biUnion E := by
    ext Q; rw [mem_union,hg Q,mem_biUnion]; constructor
    · intro h; by_cases H : ∃ i∈Y,i∈Q
      · right; obtain ⟨i,hi,hK⟩ := H; exact ⟨i,hi,he i hi ▸ mem_filter.mpr ⟨h,hK⟩⟩
      left; push Not at H; exact ⟨h,H⟩
    rintro (⟨h,-⟩|⟨i,h,e⟩); exact h
    rw [he i h] at e; exact (mem_filter.mp e).1
  change ∑ Q∈F,(∏ i∈Q,v i)=(∑ Q∈G,∏ i∈Q,v i) + ∑ i∈Y,_
  rw [hp,sum_union hk,sum_biUnion hh]; congr 1; apply sum_congr rfl
  intro i hi; unfold stock E; rw [sum_image,mul_sum]
  · apply sum_congr rfl; intro Q hq; rw [prod_insert (h0 _ _ hq)]
  intro a ha b hb hab
  change insert i a=insert i b at hab
  exact Eq.trans (erase_insert (h0 i a ha)).symm ((congr_arg (fun Q : Finset ι => Q.erase i) hab).trans (erase_insert (h0 i b hb)))

def fresco (v : ι → ℝ) (P : Leaf J) := ∑' i, if X i=P then v i else 0

def allowed (B : Leaf J) (Q : Finset ι) := Q∈accepted X B Q

def note (v : ι → ℝ) (B : Leaf J) (Q : Finset ι) : ℝ := if allowed X B Q then ∏ i∈Q,v i else 0

def fumes (v : ι → ℝ) (B : Leaf J) := ∑' Q : Finset ι,note X v B Q

lemma stock_limits {v : ι → ℝ} (he : Summable v) (B : Leaf J) : Tendsto (fun I : Finset ι => stock X v I B) atTop (𝓝 (fumes X v B)) := by
  have hh : Summable (note X v B) := by
    refine Summable.of_norm_bounded (summable_finsetProd_of_summable_nonneg (fun i=>norm_nonneg _) he.norm) (fun Q => ?_)
    unfold note; split
    · exact (norm_prod ..).le
    rw [norm_zero]; exact prod_nonneg fun i _=> norm_nonneg _
  have ht (I : Finset ι) : I.powerset.filter (allowed X B)=accepted X B I := by
    ext i; simp only [mem_filter, allowed,accepts,stays,mem_powerset]; simp
  refine (hh.hasSum.comp tendsto_finset_powerset_atTop_atTop).congr' (Eventually.of_forall ?_)
  intro i
  change ∑ Q∈i.powerset,note X v B Q=_
  unfold note; rw [← sum_filter,ht]; rfl

lemma alias_limits {v : ι → ℝ} (he : Summable v) (B : Leaf J) :
    Tendsto (fun I : Finset ι => crowd X v I B) atTop (𝓝 (fresco X v B)) := by
  have h : Summable (fun i=> if X i=B then v i else 0) := by
    apply Summable.of_norm_bounded he.norm; intro i; split; rfl
    rw [norm_zero]; exact norm_nonneg _
  exact h.hasSum

theorem shelf (hn : ∀ i,(X i).Nonempty) (v : ι → ℝ) (he : Summable v) :
    Deletion (fun P => -fresco X v P) (fumes X v) := by
  constructor
  · have hb (s : Finset ι) : stock X v s ∅=1 := by
      have hh : accepted X ∅ s ={∅} := by
        ext Q; rw [accepts,mem_singleton]; unfold stays
        simp only [subset_empty]
        constructor
        · rintro ⟨h₁,h₂,h₃⟩; exact eq_empty_iff_forall_notMem.mpr fun i hi => (hn i).ne_empty (h₂ i hi)
        rintro rfl; simp
      unfold stock; rw [hh,sum_singleton,prod_empty]
    have hl := stock_limits X he ∅; simp_rw [hb] at hl; exact tendsto_nhds_unique hl tendsto_const_nhds
  intro B x hx
  have hp := stock_limits X he B
  simp_rw [stock_deletion X B _ v hn x hx] at hp
  have ht := (stock_limits X he (B.erase x)).add (tendsto_finsetSum (owners B x) (fun P _ =>
    (alias_limits X he P).mul (stock_limits X he (B\P))))
  change _ = _ - ∑ P ∈ owners B x,_
  simp only [neg_mul,Finset.sum_neg_distrib,sub_neg_eq_add]
  exact tendsto_nhds_unique hp ht


/-- Direct label criterion, no statistical independence assumed; use e.g.
a hit at *A+1* and a ≍ (B+B+1)^{-4}. -/
structure Sufficient (w : Grid J) (v : ι → ℝ) (a δ : ℝ) : Prop where
  budget : Rate w
  nonneg i : 0 ≤ v i
  pos : 0 ≤ a
  small : δ ≤ 1 - expo (-a)
  asks x : SumBudget (fun i => if x∈X i then w (X i)*v i*expo (a*(X i).card) else 0) δ

variable {X}
lemma supplied_sum {w : Grid J} {v : ι→ℝ} {a δ : ℝ} (hn : ∀ i,(X i).Nonempty) (hh : Sufficient X w v a δ) : Summable v := by
  let q (x : J) i := if x∈X i then w (X i)*v i*expo (a*(X i).card) else 0
  have he (x : J) : SumBudget (q x) δ := hh.asks x
  have ht i : v i ≤ ∑ x : J,q x i := by
    obtain ⟨x,hx⟩ := hn i
    have hl : v i ≤ q x i := by
      unfold q; rw [if_pos hx]; exact (le_mul_of_one_le_left (hh.nonneg _) (hh.budget.pos _)).trans
        (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans (hh.budget.pos _)) (hh.nonneg _)) (Real.one_le_exp (mul_nonneg hh.pos (by positivity))))
    exact hl.trans (single_le_sum (fun j _ => (he j).1 i) (mem_univ x))
  exact (summable_sum (fun i _ => (he i).2.1)).of_nonneg_of_le hh.nonneg ht

lemma pay_fresco {w : Grid J} {v : ι→ℝ} {a δ : ℝ} (hn : ∀ i,(X i).Nonempty) (hh : Sufficient X w v a δ) :
    Receipt w (fresco X v) a := by
  have h (P : Leaf J) : 0 ≤ fresco X v P := tsum_nonneg fun i => by split; exact hh.nonneg _; rfl
  refine ⟨hh.budget,h,hh.pos,fun x => ?_⟩
  let W := fun P : Leaf J => expo (a*P.card)*w P
  let O := (univ : Finset (Leaf J)).filter (fun i => x∈i)
  have hy (i : Finset ι) : ∑ P∈O,w P*crowd X v i P*expo (a*P.card) ≤ δ := by
    apply le_trans (b:=∑ k∈i,if x∈X k then w (X k)*v k*expo (a*(X k).card) else 0) _
      (((hh.asks x).2.1.sum_le_tsum _ fun i _ => (hh.asks x).1 i).trans (hh.asks x).2.2)
    apply le_of_eq; unfold crowd; simp_rw [Finset.mul_sum,Finset.sum_mul]; rw [sum_comm]
    apply sum_congr rfl; intro j hj
    unfold O; simp_rw [mul_ite,ite_mul,mul_zero,zero_mul]
    by_cases he : x∈X j <;> simp [he]
  apply le_trans _ hh.small
  have hT := tendsto_finsetSum O (fun i (_:i∈O) => ((alias_limits X (supplied_sum hn hh) i).const_mul (w i)).mul_const (expo (a*i.card)))
  exact le_of_tendsto hT (Eventually.of_forall hy)

lemma attendance {u v : ι → ℝ} (hs : Summable v) (he : ∀ i, |u i| ≤ v i) (i : Leaf J) : |fresco X u i| ≤ fresco X v i := by
  let T := fun j => if X j=i then u j else 0
  let P := fun j => if X j=i then v j else 0
  have hp (j) : ‖T j‖ ≤ P j := by unfold T P; split; exact he j; exact (norm_zero).le
  have hT : Summable P := hs.of_nonneg_of_le (fun j => (norm_nonneg _).trans (hp j)) fun j => by
    unfold P; split; rfl; exact (abs_nonneg _).trans (he j)
  have hm := hT.of_nonneg_of_le (fun j => norm_nonneg _) hp
  exact (norm_tsum_le_tsum_norm hm).trans (hm.tsum_le_tsum hp hT)

/-- Exact log and absolute budget for the countably addressed signed
integrated coefficients (at a fixed field); common envelope for families
through those same label prices. Doesn't give the *input* equality
of Xi against a Wilson sector; use once that assembly agrees. -/
theorem catalog {w : Grid J} {v : ι→ℝ} {a δ : ℝ} (hn : ∀ i,(X i).Nonempty) (hh : Sufficient X w v a δ)
    (u : ι→ℝ) (he : ∀ i, |u i| ≤ v i) :
    Applied w (fumes X u) a (ceiling (fumes X (-v))) := by
  have ht := supplied_sum hn hh
  have hk : Deletion (fresco X v) (fumes X (-v)) := by
    have H := shelf X hn (-v) ht.neg
    rw [show (fun P => -fresco X (-v) P) = fresco X v from ?_] at H; exact H
    funext P
    unfold fresco; rw [← tsum_neg]; apply tsum_congr; intro i; split <;> simp
  exact swept (pay_fresco hn hh) hk
    (fun i => by rw [abs_neg]; exact attendance ht he i)
    (shelf X hn u (Summable.of_norm_bounded ht he))

/-- Deleting arbitrary sites after re-log. Includes empty deletion and
whole universe. This is the common ratio that multiplies a forced
family at **one** set of selected forced supports. The sign of the
omitted log contribution here is **positive of the negative-log piece**.
No exponent reweighting at unused tags. -/
theorem omitted {w : Grid J} {v : ι→ℝ} {a δ : ℝ} (hn : ∀ i,(X i).Nonempty) (hh : Sufficient X w v a δ)
    (u : ι→ℝ) (he : ∀ i, |u i| ≤ v i) (Q : Leaf J) :
    let Y := fumes X u
    let M := (univ : Finset (Leaf J)).filter fun P => (P∩Q).Nonempty
    let l := ∑ i∈M,locker Y i
    Y (univ\Q)=Y univ * Real.exp l ∧ |l| ≤ Q.card*a := by
  intro Y M l
  let g := ceiling (fumes X (-v))
  have h := catalog hn hh u he
  have H : (univ : Leaf J).powerset = Finset.univ := by ext; simp
  have ht (i : Leaf J) : i ⊆ univ\Q ↔ ¬ (i∩Q).Nonempty := by
    constructor
    · rintro h1 ⟨x,hx⟩; exact (Finset.mem_sdiff.mp (h1 (mem_inter.mp hx).1)).2 (mem_inter.mp hx).2
    intro h1 x hx; exact Finset.mem_sdiff.mpr ⟨mem_univ _, fun he => h1 ⟨x,mem_inter.mpr ⟨hx,he⟩⟩⟩
  have hp : ((univ : Leaf J)\Q).powerset = univ.filter fun i => ¬ (i∩Q).Nonempty := by ext i; rw [mem_powerset,ht,mem_filter]; simp
  constructor
  · change fumes X u _ = fumes X u _ * _
    rw [h.log_form (B:= _ \ Q), h.log_form (B:=univ),← Real.exp_add]; congr 1
    unfold shed; rw [H,hp]
    have hz := sum_filter_add_sum_filter_not univ (fun i : Leaf J => (i∩Q).Nonempty) (locker Y)
    change -(∑ i∈univ.filter (fun i : Leaf J => ¬ (i∩Q).Nonempty), locker Y i) = -(∑ i, locker Y i)+
      ∑ i∈univ.filter (fun i : Leaf J => (i∩Q).Nonempty), locker Y i
    linarith only [hz]
  have hl (i : Leaf J) : |locker Y i| ≤ w i*g i := (h.negLog i).trans
    (le_mul_of_one_le_left ((abs_nonneg _).trans (h.negLog i)) (hh.budget.pos _))
  have hy : ∀ x : J,∑ i∈univ, (if x∈i then w i*g i else 0) ≤ a := fun j => by rw [← sum_filter]; exact h.hits j
  calc
    |l| ≤ ∑ i∈M,|locker Y i| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ i,∑ x∈Q,if x∈i then w i*g i else 0 := by
      have h0 i : 0≤w i*g i := (abs_nonneg _).trans (hl i)
      apply le_trans _ (sum_le_sum_of_subset_of_nonneg (s:=M) (subset_univ _) fun i hi _ => sum_nonneg fun j hj => by split; exact h0 _; rfl)
      apply sum_le_sum; intro i hi
      apply (hl i).trans
      obtain ⟨x,hx⟩ := (mem_filter.mp hi).2; obtain ⟨h1,h2⟩ := mem_inter.mp hx
      have hk := single_le_sum (s:=Q) (f:=fun x=>if x∈i then w i*g i else 0) (fun j _ => by split; exact h0 i; rfl) h2
      rwa [if_pos h1] at hk
    _ ≤ _ := by rw [sum_comm]; exact (sum_le_sum fun i _=>hy i).trans (by simp)

end YM.SectorNext.Vacuum.ReLog
