import YM.Axis.Matrix
import YM.Extra.MULTISOURCE_BOUNDS.Germs
import YM.Extra.MULTISOURCE_BOUNDS.Numbered
import YM.Extra.MULTISOURCE_BOUNDS.Ursell
import YM.Next.EXTRACTION.Base

/-!
# Repeated-address marker-rooted overlap sums 

Root at an occurrence carrying the hit name. Numbered occurrences,
full Ursell coefficients and normalization. Site-hit and marker-root costs
can be different. Bounds use ancestor multiplicity only in making the
site-hit threshold true (e.g. by `root_hit`). Also applicable as a positive
tree sum to attachments with repeats. No logarithm identity itself proved.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi.Repeated
open Function Filter SimpleGraph Lattice Wilson RG Finset Numbered Mayer
open scoped BigOperators Topology Matrix.Norms.Frobenius Classical

variable {V α : Type*} {n : Side}

def overlap (X : α → Support n) (u : V → α) : SimpleGraph V where
  Adj i j := i ≠ j ∧ ∃ x∈ X (u i), x ∈ X (u j)
  symm := ⟨by rintro i j ⟨h,x,h1,h2⟩; exact ⟨h.symm,x,h2,h1⟩⟩
  loopless := ⟨fun _ => by simp⟩

section Finite
variable [Fintype α] [Fintype V] {X : α → Support n} {f : α → ℝ} {M : ℕ}
  {ok : α → Prop} {b γ : ℝ}

private def ed (X : α → Support n) (M : ℕ) (f : α→ℝ) (i : α) := f i * Real.exp (coverNumber M (X i))
private def transition (X : α → Support n) (M : ℕ) (f : α→ℝ) (i j : α) :=
    if Ac.meets X j (X i) then ed X M f j / coverNumber M (X i) else 0

private def track (X : α → Support n) (r : V) (ok : α → Prop) (f : α → ℝ) (p : V → V) (u : V → α) :=
    if Trunk (overlap X u) r p ∧ ok (u r) then ∏ i,f (u i) else 0

private lemma exp_charge (d : V → ℕ) (r : V) (p : V → V) :
    ∏ i∈nonroot r,(d (p i):ℝ) ≤ (∏ j, ((daughters r p j).factorial : ℝ)) * ∏ j,Real.exp (d j) := by
  rw [← prod_fiberwise (nonroot r) p,← prod_mul_distrib]
  refine prod_le_prod (fun i _ => prod_nonneg fun j _ => Nat.cast_nonneg _) fun i _ => ?_
  rw [show (∏ j∈(nonroot r).filter (fun j => p j=i),(d (p j):ℝ))=(d i)^daughters r p i by
    rw [prod_congr rfl (fun j hj => congrArg (fun i => (d i:ℝ)) (mem_filter.mp hj).2),prod_const]; rfl, mul_comm _ (Real.exp _)]
  exact (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp _ (Nat.cast_nonneg _) _)

omit [Fintype α] in
private lemma track_cap (hf : ∀ i,0≤f i) (p : V→V) (r : V) (u : V→α) :
    track X r ok f p u ≤ (∏ j, ((daughters r p j).factorial : ℝ)) * ((if ok (u r) then ed X M f (u r) else 0) *
      ∏ i∈ nonroot r,transition X M f (u (p i)) (u i)) := by
  -- `nonroot` and `daughters` always use exactly the same pinned instances.
  unfold track; split <;> rename_i h
  · obtain ⟨⟨hp,d,hd⟩,h⟩ := h
    let m i := coverNumber M (X (u i))
    have hm i (hi : i∈nonroot r) : transition X M f (u (p i)) (u i) = ed X M f (u i)/m (p i) ∧
        0 < (m (p i):ℝ) := by
      obtain ⟨x,hx,he⟩ := ((hd i (ne_of_mem_erase hi)).2).2
      have ht := Corona.pays (X (u (p i))) M
      have h := card_pos.mpr ⟨x,he⟩
      exact ⟨if_pos ⟨_,he,hx⟩, Nat.cast_pos.mpr (by unfold m; by_contra! hz; rw [Nat.eq_zero_of_le_zero hz,zero_mul] at ht; omega)⟩
    rw [if_pos h,prod_congr rfl fun i hi => (hm i hi).1,prod_div_distrib,← mul_div_assoc,← mul_div_assoc,le_div_iff₀ (prod_pos (fun i hi => (hm i hi).2)),nonroot,
      show ed X M f (u r)*(∏ x∈univ.erase r,ed X M f (u x)) = ∏ x, ed X M f (u x) from mul_prod_erase _ (fun x => ed X M f (u x)) (mem_univ r)]
    apply (mul_le_mul_of_nonneg_left (exp_charge m r p) (prod_nonneg fun i (_:i∈univ) => hf (u i))).trans_eq
    unfold ed; rw [prod_mul_distrib]; ring
  have he (i) : 0 ≤ ed X M f i := mul_nonneg (hf i) (Real.exp_pos _).le
  have hk (i j) : 0 ≤ transition X M f i j := by unfold transition; split; exact div_nonneg (he j) (by positivity); exact le_rfl
  split <;> first | exact mul_nonneg (prod_nonneg fun j _ => Nat.cast_nonneg _) (mul_nonneg (he _) (prod_nonneg fun i _ => hk ..)) | simp

lemma fixed_parent (hf : ∀ i,0 ≤ f i) (hγ : 0 ≤ γ) (hk : Ac.Hit X M f 1 γ) (hb : 0 ≤ b)
    (h : SumBudget (fun i => if ok i then f i * Real.exp (coverNumber M (X i)) else 0) b)
    (r : V) (p : V → V) : ∑ u, track X r ok f p u ≤
      (∏ j, ((daughters r p j).factorial : ℝ)) * ((((M+M+1:ℕ):ℝ)^4 * γ) ^ (nonroot r).card * b) := by
  let F (i) := if ok i then ed X M f i else 0
  let K := transition X M f
  let Z := ((M+M+1:ℕ):ℝ)^4*γ
  have hF (i) : 0≤F i := h.1 i
  have hK (i j) : 0 ≤ K i j := by
    unfold K transition ed; split; exact div_nonneg (mul_nonneg (hf _) (Real.exp_pos _).le) (Nat.cast_nonneg _); exact le_rfl
  have hZ i : ∑ j,K i j ≤ Z := by
    by_cases hm : coverNumber M (X i) = 0
    · simp only [K,transition,hm,Nat.cast_zero,div_zero,ite_self,sum_const_zero]; unfold Z; positivity
    have hd := Ac.demand X M hk (X i) univ
    rw [show ∑ j,K i j = _ from Eq.symm (sum_filter (fun j => Ac.meets X j (X i)) _), ← sum_div,
      div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))]
    simp only [one_mul] at hd
    refine hd.trans ?_
    have he : ((X i).card:ℝ) ≤ _ := Nat.cast_le (α:=ℝ).mpr <| Corona.pays (X i) M
    unfold Z; push_cast at he ⊢
    linarith only [mul_le_mul_of_nonneg_right he hγ]
  by_cases ht : ∃ u : V → α, Trunk (overlap X u) r p
  · obtain ⟨u,hp,d,hd⟩ := ht
    refine (sum_le_sum (fun i _ => track_cap (M:=M) hf p r i)).trans ?_
    rw [← mul_sum]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun _ _ => Nat.cast_nonneg _)
    exact (cascade r p d (fun i hi => (hd i hi).1) F K Z hF hK hZ).trans (mul_le_mul_of_nonneg_left (Budget.cap h _) (by positivity))
  push Not at ht
  simp only [track, ht, false_and,↓reduceIte,sum_const_zero]; exact mul_nonneg (prod_nonneg fun _ _ => Nat.cast_nonneg _) (by positivity)

lemma assignments (hf : ∀ i,0 ≤ f i) (hγ : 0 ≤ γ) (hk : Ac.Hit X M f 1 γ) (hb : 0 ≤ b)
    (h : SumBudget (fun i => if ok i then f i * Real.exp (coverNumber M (X i)) else 0) b)
    (r : V) : (∑ u : V→α, if ok (u r) then ((spans (overlap X u) r).card : ℝ)*(∏ j,f (u j)) else 0) ≤
      ((nonroot r).card.factorial:ℝ)*((4*((M+M+1:ℕ):ℝ)^4*γ) ^ (nonroot r).card * b) := by
  let S := univ.filter (fun p : V→V => p r=r)
  have he u : ∑ p∈S, track X r ok f p u = if ok (u r) then ((spans (overlap X u) r).card : ℝ)*(∏ j,f (u j)) else 0 := by
    by_cases h : ok (u r)
    · have ht : S.filter (Trunk (overlap X u) r) = spans (overlap X u) r := Finset.ext fun i => by
        simp [S,spans,and_iff_right_of_imp (show Trunk (overlap X u) r i → i r=r from fun ht => ht.1)]
      simp [track,h,← sum_filter,ht]
    simp [track,h]
  let Z := (((M+M+1:ℕ):ℝ)^4*γ)^(nonroot r).card*b
  have hZ : 0≤Z := by unfold Z; positivity
  simp_rw [← he]; rw [sum_comm]; apply (sum_le_sum fun i _ => fixed_parent hf hγ hk hb h r i).trans
  rw [← sum_mul]; exact (mul_le_mul_of_nonneg_right (allotted r) hZ).trans_eq (by unfold Z; ring)

end Finite

abbrev Tuple (α : Type*) := (k : ℕ) × (Fin (k+1) → α)

def numbered (X : α→Support n) (u : Tuple α) : Support n := univ.biUnion fun i => X (u.2 i)

lemma joins (X : α→Support n) (u : Tuple α) (h : (overlap X u.2).Connected) (M) :
    coverNumber M (numbered X u) ≤ ∑ i, coverNumber M (X (u.2 i)) := Ac.cover _ M ⟨univ_nonempty,fun i _ j _ => by
      induction reachable_iff_reflTransGen _ _ |>.mp (h i j) with
      | refl => exact .refl
      | tail _ he ih => exact (ih (mem_univ _)).tail ⟨mem_univ _,mem_univ _,he.2⟩⟩

def worth (f : α → ℝ) (c : Tuple α → ℝ) (u : Tuple α) : ℝ := c u / (u.1+1).factorial * ∏ i,f (u.2 i)

theorem repeated (X : α → Support n) (M) (f : α → ℝ) (coef : Tuple α → ℝ) (ok : α → Prop) (b γ a : ℝ)
    (hb : 0≤b) (hγ : 0 ≤ γ) (hZ : 8*((M+M+1:ℕ):ℝ)^4*γ ≤ 1) (ha : 0 ≤ a) (hf : ∀ i,0 ≤ f i)
    (hc : ∀ u, 0≤coef u ∧ ∀ r, coef u ≤ (spans (overlap X u.2) r).card) (hk : Ac.Hit X M f (a+1) γ)
    (h : SumBudget (fun i => if ok i then Real.exp ((a+1)*coverNumber M (X i)) * f i else 0) b) :
    SumBudget (fun u : Tuple α => if ∃ i, ok (u.2 i) then Real.exp (a*coverNumber M (numbered X u))*worth f coef u else 0) (2*b) := by
  let g (u : Tuple α) := if ∃ i,ok (u.2 i) then Real.exp (a*coverNumber M (numbered X u))*worth f coef u else 0
  let w (i : α) := Real.exp (a*coverNumber M (X i)) * f i
  let W (u : Tuple α) (i : Fin (u.1+1)) := if ok (u.2 i) then ((spans (overlap X u.2) i).card:ℝ)*∏ j,w (u.2 j) else (0:ℝ)
  have hW u i : 0 ≤ W u i := by
    unfold W; split
    next => exact mul_nonneg (by positivity) (prod_nonneg fun j _ => mul_nonneg (Real.exp_pos _).le (hf _))
    exact le_rfl
  have hg u : 0 ≤ g u ∧ (u.1+1).factorial * g u ≤ ∑ i,W u i := by
    unfold g; split <;> rename_i h
    · obtain ⟨r,hr⟩ := h
      have he : 0 < ((u.1+1).factorial:ℝ) := by positivity
      rw [worth,show (_:ℝ)*(_*(_ / _ *_)) = Real.exp (a*coverNumber M (numbered X u))*(∏ i,f (u.2 i)) * coef u by field_simp]
      have hy := mul_nonneg (Real.exp_pos (a*coverNumber M (numbered X u))).le (prod_nonneg (s:=univ) fun i (_:i∈univ) => hf (u.2 i))
      refine ⟨mul_nonneg (Real.exp_pos _).le (mul_nonneg (div_nonneg (hc u).1 he.le) (prod_nonneg fun _ _ => hf _)),?_⟩
      apply le_trans _ (single_le_sum (fun i _ => hW u i) (mem_univ r))
      change _ ≤ W u r; rw [show W u r = _ from if_pos hr]; unfold w; rw [prod_mul_distrib, ← Real.exp_sum,← mul_sum, mul_comm ((spans _ r).card:ℝ)]
      by_cases hx : (overlap X u.2).Connected
      · gcongr
        · exact (hc u).1
        · exact mul_nonneg (Real.exp_pos _).le (prod_nonneg fun i _ => hf _)
        · exact prod_nonneg fun i _ => hf _
        · exact_mod_cast joins _ _ hx M
        exact (hc u).2 r
      have hspan : (spans (overlap X u.2) r).card=0 := by
        contrapose! hx; obtain ⟨p,hp⟩ := card_pos.mp (Nat.pos_of_ne_zero hx)
        obtain ⟨hr,d,hd⟩ := (mem_filter.mp hp).2
        have he (k : ℕ) : ∀ i,d i=k → (overlap X u.2).Reachable i r := by
          induction k using Nat.strong_induction_on with
          | _ k ih =>
          intro i hi; by_cases h : i=r
          · rw [h]
          exact (hd _ h).2.reachable.trans (ih _ ((hd _ h).1.trans_eq hi) _ rfl)
        exact (connected_iff_exists_forall_reachable _).mpr ⟨r,fun i => (he _ i rfl).symm⟩
      simp only [hspan,Nat.cast_zero,mul_zero]; exact mul_nonpos_of_nonneg_of_nonpos hy ((hc u).2 r |>.trans (by simp [hspan]))
    simp only [le_refl,mul_zero,true_and]; exact sum_nonneg fun i _ => hW u i
  refine Budget.certify (fun u => (hg u).1) (fun t => ?_)
  let A := t.biUnion fun u => univ.image u.2
  have h' : SumBudget (fun i : A => if ok (i:α) then w i * Real.exp (coverNumber M (X i)) else 0) b := by
    apply Budget.pull_le (p:=fun _ => True) (q:=Subtype.val) h
    · intro i; split; exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (hf _)) (Real.exp_pos _).le; exact le_rfl
    · exact fun _ _ => trivial
    · exact Subtype.val_injective.injOn
    simp [w,Real.exp_add,add_mul,mul_assoc,mul_left_comm]; exact fun i _ => by split <;> ring_nf <;> rfl
  have H' : Ac.Hit (fun i : A => X i.val) M (fun i => w i.val) 1 γ := by
    intro y
    apply Budget.pull_le (p:=fun _ => True) (q:=Subtype.val) (hk y)
    · intro i; split; exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (hf _)) (Real.exp_pos _).le; exact le_rfl
    · exact fun _ _ => trivial
    · exact Subtype.val_injective.injOn
    intro i _; dsimp only; split_ifs <;> simp [w,add_mul,Real.exp_add,mul_assoc,mul_left_comm]
  let pack (k : ℕ) (v : Fin (k+1) → A) := (⟨k,fun i => (v i).val⟩ : Tuple α)
  have cap (k : ℕ) : ∑ u, g (pack k u) ≤ ((1/2:ℝ)^k*b) := by
    have H (i : Fin (k+1)) := assignments (fun q : A => mul_nonneg (Real.exp_pos _).le (hf q.val)) hγ H' hb h' i
    have he (i : Fin (k+1)) : (nonroot i).card=k := by simpa using nonroot_card i
    have he' : 0 < ((k+1).factorial:ℝ) := by positivity
    apply le_of_mul_le_mul_left _ he'
    calc
      _ = ∑ u,(k+1).factorial * g (pack k u) := mul_sum ..
      _ ≤ ∑ i : Fin (k+1),∑ u,W (pack k u) i := by rw [sum_comm]; exact sum_le_sum fun i _ => (hg (pack k i)).2
      _ ≤ ∑ _ : Fin (k+1), (k.factorial:ℝ)*((4*((M+M+1:ℕ):ℝ)^4*γ)^k*b) := by
        apply sum_le_sum; intro i _; have h := H i; rw [he i] at h; convert! h using 2; ext; simp
      _ = (k+1).factorial*((4*((M+M+1:ℕ):ℝ)^4*γ)^k*b) := by simp [Nat.factorial_succ,mul_assoc]
      _ ≤ _ := by gcongr; linarith only [hZ]
  let S := t.image Sigma.fst
  have hf (u) (hu : u∈t) : ∃ k∈S, ∃ v,u=pack k v := ⟨u.1,mem_image_of_mem _ hu,fun i =>
      ⟨_,mem_biUnion.mpr ⟨u,hu,mem_image_of_mem _ (mem_univ i)⟩⟩,rfl⟩
  have he := hasSum_geometric_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)
  calc
    _ ≤ ∑ u∈(S.sigma (fun k => (univ : Finset (Fin (k+1) → A)))).image (fun u => pack u.1 u.2),g u :=
      sum_le_sum_of_subset_of_nonneg (fun i hi => (by obtain ⟨k,hk,v,rfl⟩ := hf _ hi; exact mem_image_of_mem _ (show (⟨k,v⟩:(k:ℕ) × (Fin (k+1) → A))∈S.sigma fun _ => univ from mem_sigma.mpr ⟨hk,mem_univ _⟩)))
        (fun _ _ _ => (hg _).1)
    _ ≤ ∑ k∈S, ∑ v,g (pack k v) := (sum_image_le_of_nonneg (fun _ _ => (hg _).1)).trans (by rw [sum_sigma])
    _ ≤ (∑ k∈S, (1/2:ℝ)^k)*b := by rw [sum_mul]; exact sum_le_sum fun i _ => cap i
    _ ≤ _ := mul_le_mul_of_nonneg_right ((he.summable.sum_le_tsum _ (fun _ _ => by positivity)).trans_eq (by rw [he.tsum_eq]; norm_num)) hb

end YM.Extra.Multi.Repeated
