import YM.Next.MULTISOURCE.Enclosure
import YM.Next.MULTISOURCE.Stale

/-! pricing and rooted support of ONE response from scalar -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open RG Wilson Lattice Filter Finset MeasureTheory MvPolynomial
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I : Type} [Fintype I] [DecidableEq I] {G : Gauge} {n : Side}
variable {P : Rep G n} {κ : ℝ}

lemma joined (P : BudgetPoint) (q : Pack n) (F : ℕ → Config G n → ℂ) (h : ∀ i, Legible P q (F i)) :
    Legible P q (fun x => ∑' j,F j x) := by
  refine ⟨Measurable.tsum (fun i => (h i).borel), fun j x => tsum_congr fun i => (h i).symmetry j x,
    fun U V H H' => tsum_congr fun i => (h i).reads U V H H',?_⟩
  intro U H; by_contra he
  exact H ((tsum_congr (g:=fun _ => (0:ℂ)) (fun i => by by_contra hh; exact he ((h i).inventory U hh))).trans tsum_zero)

lemma pawn_H (T : Reservoir P I) (X : I→Support n) (q : Grade I) {r : ℝ} (he : 0 < r) {A : Set (I → ℂ)} {R : I→Support n → Prop}
    (hx : boxes r ⊆ A) (H : T.Shelved A R) (ht : ∀ i∈q.support, ∀ Y,R i Y → X i ⊆ Y) (i : ℕ)
    (hK : ¬ (q.support.biUnion X) ⊆ T.support i) : bite T q i=0 := by
  suffices ∃ j∈q.support, ¬ R j (T.support i) by
    obtain ⟨j,hj,hj'⟩ := this
    exact funext fun x => sleeps A he hx j (T.D i x) (H.trust j i x hj') q hj
  by_contra hh; push Not at hh
  apply hK; exact biUnion_subset.mpr fun j hj => ht _ hj _ (hh j hj)

lemma pawn_K (T : Reservoir P I) (X : I→Support n) (q : Grade I) {r : ℝ} (he : 0 < r) {A : Set (I → ℂ)} {R : I→Support n → Prop}
    (hx : boxes r ⊆ A) (H : T.Shelved A R) (ht : ∀ i∈q.support, ∀ Y,R i Y → X i ⊆ Y) (i : ℕ)
    (hK : ¬ (q.support.biUnion X) ⊆ (T.k i).zone) : chew T q i=0 := by
  suffices ∃ j∈q.support, ¬ R j (T.k i).zone by
    obtain ⟨j,hj,hj'⟩ := this
    exact funext fun x => sleeps A he hx j (T.K i x) (H.rent j i x hj') q hj
  by_contra hh; push Not at hh
  apply hK; exact biUnion_subset.mpr fun j hj => ht _ hj _ (hh j hj)

lemma pawns (T : Reservoir P I) (o : I→Site n) (k : I→ℝ) (ρ : ℝ) (hk : ∀ i,0 ≤ k i) (ht : 0 < ρ)
    {R : I → Support n → Prop} (H : T.Tested κ (allot o k ρ)) (h : T.Shelved (allot o k ρ) R) (X : I→Support n)
    (S : Finset I) (hκ : 0 < κ) (hs : Set.InjOn o S) (hm : (S.biUnion X).Nonempty)
    (hx : ∀ i∈S,∀ Y, R i Y → X i ⊆ Y) (hp : coeff (power S) (staves T.pay)=0) :
    Credit P.p 2 κ (S.biUnion X) (T.taste (power S)) (ρ⁻¹^S.card * ∏ j∈S, k j) := by
  obtain ⟨ht',hg,hH,hG⟩ := gained T o k ρ hk ht H S hs
  let q := power S
  let A := S.biUnion X
  let C := ρ⁻¹^S.card * ∏ j∈S,k j
  obtain ⟨r,hr,hR⟩ := permits o k ρ hk ht
  have hb : 0 ≤ C := mul_nonneg (by positivity) (prod_nonneg fun i _ => hk _)
  let w i := if A ⊆ T.support i then mints T q i else 0
  let L i := if A ⊆ T.support i then T.support i else A
  let W i := if A ⊆ T.support i then bite T q i else 0
  refine ⟨hm,by norm_num,hκ,hb,⟨0,(fun U => ∑' i, coeff q (T.keeps i U)),by simp only [Reservoir.taste,hp,q],fun _ => rfl,
    (norm_zero).trans_le hb, L,W,w,?_,?_,?_⟩,?_⟩
  · intro i; by_cases he : A ⊆ T.support i
    · simp only [L,W,w, he,↓reduceIte]; exact ⟨he,(ht' i).1,(ht' i).2.1,fun j hj => (ht' i).2.2 _ (he hj)⟩
    simp only [L,W,w,he,↓reduceIte]; exact ⟨subset_refl A,(null_path ..).1,le_rfl,fun j _ => (null_path ..).2 _⟩
  · obtain ⟨x,hx'⟩ := hm
    refine permit_le (hH x) le_rfl fun i => ?_
    by_cases he : A ⊆ T.support i
    · simp only [L,w,he, he hx',↓reduceIte]; exact ⟨mul_nonneg (burn_pos ..).le (ht' i).2.1,le_rfl⟩
    simp only [w,he,↓reduceIte,mul_zero]; exact ⟨le_rfl,(hH x).1 i⟩
  · intro U; apply tsum_congr; intro i
    by_cases he : A ⊆ T.support i
    · simp only [W,L,he,↓reduceIte]; by_cases hd : Healthy P.p.threshold (T.support i) U
      · unfold Reservoir.keeps; rw [masked_eq _ _ _ _ hd,masked_eq _ _ _ _ hd]; rfl
      unfold Reservoir.keeps; rw [masked_ne _ _ _ _ hd, masked_ne _ _ _ _ hd]; exact coeff_zero _
    have hh : bite T q i=0 := pawn_H T X q hr hR h (by simpa only [q,support_power] using hx) i (by
      simpa only [q,support_power] using he)
    simp only [L,W,he,↓reduceIte]; unfold Reservoir.keeps; by_cases hd : Healthy P.p.threshold (T.support i) U
    · rw [masked_eq _ _ _ _ hd, show coeff q (T.D i U)=0 from congr_fun hh U]; simp [masked]
    rw [masked_ne _ _ _ _ hd]; simp [masked]
  let f i := if A ⊆ (T.k i).zone then tolls T q i else 0
  let Y (b : Pack n) (i : ℕ) := if b=T.k i then f i else 0
  let J (b : Pack n) (i : ℕ) := fun U => coeff q (T.records b i U)
  have hK i (he : ¬ A ⊆ (T.k i).zone) : chew T q i=0 := pawn_K T X q hr hR h
    (by simpa only [q,support_power] using hx) i (by simpa only [q,support_power] using he)
  obtain ⟨x,hx'⟩ := hm
  have hf i : 0 ≤ f i := by unfold f; split; exact (hg i).2.1; exact le_rfl
  have hu : SumBudget (fun i => burn P.p 2 (T.k i).zone*f i) (κ*C) := by
    refine permit_le (hG x) le_rfl fun i => ⟨mul_nonneg (burn_pos ..).le (hf i),?_⟩
    unfold f; split <;> rename_i he
    · rw [if_pos (he hx')]
    rw [mul_zero]; exact (hG x).1 i
  have hb : Summable f := hu.2.1.of_nonneg_of_le hf
    (fun i => le_mul_of_one_le_left (hf i) (burn_ge P.p (by norm_num) _))
  have hy b i : 0 ≤ Y b i ∧ Y b i ≤ f i := by
    unfold Y; split; exact ⟨hf i,le_rfl⟩; exact ⟨le_rfl,hf i⟩
  have hY b : Summable (Y b) := hb.of_nonneg_of_le (fun i => (hy b i).1) (fun i => (hy b i).2)
  have hz b i : Legible P.p b (J b i) ∧ ∀ U, ‖J b i U‖ ≤ Y b i := by
    by_cases he : b=T.k i
    · subst b; simp only [J,Reservoir.records, Y, if_true]; refine ⟨(hg i).1, fun U => ?_⟩
      change ‖chew T q i U‖ ≤ _; unfold f; split
      · exact (hg i).2.2 U
      rename_i h; simp [hK _ h]
    simp only [J,Reservoir.records,Y,he,↓reduceIte,coeff_zero,norm_zero]
    exact ⟨Legible.zero ..,fun _ => le_rfl⟩
  refine ⟨fun i => ∑' j, Y i j,?_,fun i => ?_⟩
  · simp_rw [← tsum_mul_left, ← Summable.tsum_finsetSum (f:=fun b (j:ℕ) => burn P.p 2 b.zone * Y b j) (s:=univ)
        (by intro b _; exact (hY _).mul_left _)]
    have hU i : ∑ b,burn P.p 2 b.zone*Y b i=burn P.p 2 (T.k i).zone*f i := by simp [Y]
    simp_rw [hU]; exact hu.2.2
  refine ⟨joined P.p i (J i) (fun j => (hz i j).1),fun H' => ?_,tsum_nonneg (fun j => (hy i j).1), fun U => ?_⟩
  · by_contra hh
    apply H'; funext U
    change ∑' j, J i j U=0
    refine (tsum_congr (g:= fun _ => 0) fun j => ?_).trans tsum_zero
    apply norm_le_zero_iff.mp; apply ((hz i j).2 U).trans_eq
    by_cases he : i=T.k j
    · exact (show Y i j=f j from if_pos he).trans (show f j=0 from if_neg (he ▸ hh))
    exact if_neg he
  have he j := (hz i j).2 U
  have ht' := (hY _).of_nonneg_of_le (fun j => norm_nonneg (J i j U)) he
  exact (norm_tsum_le_tsum_norm ht').trans (ht'.tsum_le_tsum he (hY _))
end YM.Multi.Desk
